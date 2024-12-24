Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FUNCTION_FACTORS_RIGHT_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import SKOLEM_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18934_spec.
Require Import thm18935_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Lemma lem3581232 {A B : Type'} (P : type1413 A B) (h1 : (term0 A B P) = (term1 A B P)) : (term0 A B P) = (term1 A B P).
Proof. exact (h1). Qed.
Lemma lem3581233 {A B : Type'} (P : type1413 A B) (h1 : (term0 A B P) = (term1 A B P)) : (term1 A B P) = (term0 A B P).
Proof. exact (SYM (@lem3581232 A B P h1)). Qed.
Lemma lem3581234 {A B : Type'} (P : type1413 A B) (h1 : (term1 A B P) = (term0 A B P)) : (term1 A B P) = (term0 A B P).
Proof. exact (h1). Qed.
Lemma lem3581235 {A B : Type'} (P : type1413 A B) (h1 : (term1 A B P) = (term0 A B P)) : (term0 A B P) = (term1 A B P).
Proof. exact (SYM (@lem3581234 A B P h1)). Qed.
Lemma lem3581236 {A B : Type'} (P : type1413 A B) : ((term0 A B P) = (term1 A B P)) = ((term1 A B P) = (term0 A B P)).
Proof. exact (prop_ext (fun h1 : (term0 A B P) = (term1 A B P) => @lem3581233 A B P h1) (fun h1 : (term1 A B P) = (term0 A B P) => @lem3581235 A B P h1)). Qed.
Lemma lem3581237 {A B : Type'} : (term2 A B) = (term3 A B).
Proof. exact (fun_ext (fun P : type1413 A B => @lem3581236 A B P)). Qed.
Lemma lem3581238 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3581239 {A B : Type'} : (term4 A B) = (term5 A B).
Proof. exact (MK_COMB (@lem3581238 A B) (@lem3581237 A B)). Qed.
Lemma lem3581240 {A B : Type'} : term5 A B.
Proof. exact (EQ_MP (@lem3581239 A B) (@lem13546 A B)). Qed.
Lemma lem3581241 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem3581240 A B P). Qed.
Lemma lem3581242 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term1 A B P) = (term0 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem3581271 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term0 A B P).
Proof. exact (EQ_MP (@lem3581242 A B P) (@lem3581241 A B P)). Qed.
Lemma lem3581272 {_91858 _91859 : Type'} (P : type1470 _91858 _91859) : (term7 _91858 _91859 P) = (term8 _91858 _91859 P).
Proof. exact (@lem3581271 _91859 _91858 P). Qed.
Lemma lem3581273 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term9 _91854 _91858 _91859 P f g) = (term10 _91854 _91858 _91859 P f g).
Proof. exact (@lem3581272 _91858 _91859 (term11 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581274 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term12 _91854 _91858 _91859 P f g x) = (term13 _91854 _91858 _91859 P f x g).
Proof. exact (eq_refl (term12 _91854 _91858 _91859 P f g x)). Qed.
Lemma lem3581275 {_91858 _91859 : Type'} (h : _91859 -> _91858) (x : _91859) : (h x) = (h x).
Proof. exact (eq_refl (h x)). Qed.
Lemma lem3581276 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (x : _91859) : (term14 _91854 _91858 _91859 P f g h x) = (term15 _91854 _91858 _91859 P f g h x).
Proof. exact (MK_COMB (@lem3581274 _91854 _91858 _91859 P f x g) (@lem3581275 _91858 _91859 h x)). Qed.
Lemma lem3581277 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (x : _91859) : (term15 _91854 _91858 _91859 P f g h x) = (term16 _91854 _91858 _91859 P f g h x).
Proof. exact (eq_refl (term15 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3581278 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (x : _91859) : (term14 _91854 _91858 _91859 P f g h x) = (term16 _91854 _91858 _91859 P f g h x).
Proof. exact (TRANS (@lem3581276 _91854 _91858 _91859 P f g h x) (@lem3581277 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3581279 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term17 _91854 _91858 _91859 P f g h) = (term18 _91854 _91858 _91859 P f g h).
Proof. exact (fun_ext (fun x : _91859 => @lem3581278 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3581280 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581281 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term19 _91854 _91858 _91859 P f g h) = (term20 _91854 _91858 _91859 P f g h).
Proof. exact (MK_COMB (@lem3581280 _91859) (@lem3581279 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3581282 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term21 _91854 _91858 _91859 P f g) = (term22 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun h : _91859 -> _91858 => @lem3581281 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3581283 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3581284 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term9 _91854 _91858 _91859 P f g) = (term23 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581283 _91858 _91859) (@lem3581282 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581286 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term24 _91854 _91858 _91859 P f g) = (term25 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581285) (@lem3581284 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581287 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term12 _91854 _91858 _91859 P f g x) = (term13 _91854 _91858 _91859 P f x g).
Proof. exact (eq_refl (term12 _91854 _91858 _91859 P f g x)). Qed.
Lemma lem3581288 {_91858 : Type'} (h : _91858) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem3581289 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term26 _91854 _91858 _91859 P f g x h) = (term27 _91854 _91858 _91859 P f x g h).
Proof. exact (MK_COMB (@lem3581287 _91854 _91858 _91859 P f x g) (@lem3581288 _91858 h)). Qed.
Lemma lem3581290 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term27 _91854 _91858 _91859 P f x g h) = (term28 _91854 _91858 _91859 P f x g h).
Proof. exact (eq_refl (term27 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581291 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term26 _91854 _91858 _91859 P f g x h) = (term28 _91854 _91858 _91859 P f x g h).
Proof. exact (TRANS (@lem3581289 _91854 _91858 _91859 P f x g h) (@lem3581290 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581292 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term29 _91854 _91858 _91859 P f g x) = (term13 _91854 _91858 _91859 P f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581291 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581293 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581294 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term30 _91854 _91858 _91859 P f g x) = (term31 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581293 _91858) (@lem3581292 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581295 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term32 _91854 _91858 _91859 P f g) = (term33 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581294 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581296 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581297 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term10 _91854 _91858 _91859 P f g) = (term34 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581296 _91859) (@lem3581295 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581298 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term9 _91854 _91858 _91859 P f g) = (term10 _91854 _91858 _91859 P f g)) = ((term23 _91854 _91858 _91859 P f g) = (term34 _91854 _91858 _91859 P f g)).
Proof. exact (MK_COMB (@lem3581286 _91854 _91858 _91859 P f g) (@lem3581297 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581299 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term23 _91854 _91858 _91859 P f g) = (term34 _91854 _91858 _91859 P f g).
Proof. exact (EQ_MP (@lem3581298 _91854 _91858 _91859 P f g) (@lem3581273 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581312 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term35 _91854 _91858 _91859 P g f) = (term35 _91854 _91858 _91859 P g f).
Proof. exact (eq_refl (term35 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581313 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term36 _91854 _91858 _91859 P g f) = (term23 _91854 _91858 _91859 P f g)) = ((term36 _91854 _91858 _91859 P g f) = (term34 _91854 _91858 _91859 P f g)).
Proof. exact (MK_COMB (@lem3581312 _91854 _91858 _91859 P g f) (@lem3581299 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581316 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) : (term37 _91854 _91858 _91859 P f) = (term38 _91854 _91858 _91859 P f).
Proof. exact (fun_ext (fun g : _91858 -> _91854 => @lem3581313 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581317 {_91854 _91858 : Type'} : (@all (_91858 -> _91854)) = (@all (_91858 -> _91854)).
Proof. exact (eq_refl (@all (_91858 -> _91854))). Qed.
Lemma lem3581318 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) : (term39 _91854 _91858 _91859 P f) = (term40 _91854 _91858 _91859 P f).
Proof. exact (MK_COMB (@lem3581317 _91854 _91858) (@lem3581316 _91854 _91858 _91859 P f)). Qed.
Lemma lem3581323 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) : (term41 _91854 _91858 _91859 P) = (term42 _91854 _91858 _91859 P).
Proof. exact (fun_ext (fun f : _91859 -> _91854 => @lem3581318 _91854 _91858 _91859 P f)). Qed.
Lemma lem3581324 {_91854 _91859 : Type'} : (@all (_91859 -> _91854)) = (@all (_91859 -> _91854)).
Proof. exact (eq_refl (@all (_91859 -> _91854))). Qed.
Lemma lem3581325 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) : (term43 _91854 _91858 _91859 P) = (term44 _91854 _91858 _91859 P).
Proof. exact (MK_COMB (@lem3581324 _91854 _91859) (@lem3581323 _91854 _91858 _91859 P)). Qed.
Lemma lem3581330 {_91854 _91858 _91859 : Type'} : (term45 _91854 _91858 _91859) = (term46 _91854 _91858 _91859).
Proof. exact (fun_ext (fun P : _91859 -> Prop => @lem3581325 _91854 _91858 _91859 P)). Qed.
Lemma lem3581331 {_91859 : Type'} : (@all (_91859 -> Prop)) = (@all (_91859 -> Prop)).
Proof. exact (eq_refl (@all (_91859 -> Prop))). Qed.
Lemma lem3581332 {_91854 _91858 _91859 : Type'} : (term47 _91854 _91858 _91859) = (term48 _91854 _91858 _91859).
Proof. exact (MK_COMB (@lem3581331 _91859) (@lem3581330 _91854 _91858 _91859)). Qed.
Lemma lem3581337 {_91854 _91858 _91859 : Type'} : (term48 _91854 _91858 _91859) = (term47 _91854 _91858 _91859).
Proof. exact (SYM (@lem3581332 _91854 _91858 _91859)). Qed.
Lemma lem3581339 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3581340 {_91854 _91858 _91859 : Type'} : (term48 _91854 _91858 _91859) = (term50 _91854 _91858 _91859).
Proof. exact (@lem3581339 (term48 _91854 _91858 _91859)). Qed.
Lemma lem3581341 {_91854 _91858 _91859 : Type'} : (term50 _91854 _91858 _91859) = (term48 _91854 _91858 _91859).
Proof. exact (SYM (@lem3581340 _91854 _91858 _91859)). Qed.
Lemma lem3581342 {_91854 _91858 _91859 : Type'} (h1 : term51 _91854 _91858 _91859) : term51 _91854 _91858 _91859.
Proof. exact (h1). Qed.
Lemma lem3581345 {_91854 _91858 _91859 : Type'} (h1 : term50 _91854 _91858 _91859) : term50 _91854 _91858 _91859.
Proof. exact (h1). Qed.
Lemma lem3581346 {_91854 _91858 _91859 : Type'} : term52 _91854 _91858 _91859.
Proof. exact (fun h0 : term50 _91854 _91858 _91859 => @lem3581345 _91854 _91858 _91859 h0). Qed.
Lemma lem3581347 {_91854 _91858 _91859 : Type'} (h1 : term52 _91854 _91858 _91859) : term52 _91854 _91858 _91859.
Proof. exact (h1). Qed.
Lemma lem3581348 {_91854 _91858 _91859 : Type'} (h1 : term50 _91854 _91858 _91859) : term50 _91854 _91858 _91859.
Proof. exact (h1). Qed.
Lemma lem3581349 {_91854 _91858 _91859 : Type'} (h1 : term50 _91854 _91858 _91859) (h2 : term52 _91854 _91858 _91859) : term50 _91854 _91858 _91859.
Proof. exact (@lem3581347 _91854 _91858 _91859 h2 (@lem3581348 _91854 _91858 _91859 h1)). Qed.
Lemma lem3581350 {_91854 _91858 _91859 : Type'} (h1 : term50 _91854 _91858 _91859) : term53 _91854 _91858 _91859.
Proof. exact (fun h0 : term52 _91854 _91858 _91859 => @lem3581349 _91854 _91858 _91859 h1 h0). Qed.
Lemma lem3581351 {_91854 _91858 _91859 : Type'} (h1 : term52 _91854 _91858 _91859) : term52 _91854 _91858 _91859.
Proof. exact (h1). Qed.
Lemma lem3581352 {_91854 _91858 _91859 : Type'} (h1 : term50 _91854 _91858 _91859) (h2 : term52 _91854 _91858 _91859) : term50 _91854 _91858 _91859.
Proof. exact (@lem3581350 _91854 _91858 _91859 h1 (@lem3581351 _91854 _91858 _91859 h2)). Qed.
Lemma lem3581353 {_91854 _91858 _91859 : Type'} (h1 : term52 _91854 _91858 _91859) : term52 _91854 _91858 _91859.
Proof. exact (fun h0 : term50 _91854 _91858 _91859 => @lem3581352 _91854 _91858 _91859 h0 h1). Qed.
Lemma lem3581354 {_91854 _91858 _91859 : Type'} : term54 _91854 _91858 _91859.
Proof. exact (fun h0 : term52 _91854 _91858 _91859 => @lem3581353 _91854 _91858 _91859 h0). Qed.
Lemma lem3581357 {_91854 _91858 _91859 : Type'} : term52 _91854 _91858 _91859.
Proof. exact (@lem3581354 _91854 _91858 _91859 (@lem3581346 _91854 _91858 _91859)). Qed.
Lemma lem3581358 {_91854 _91858 _91859 : Type'} : term52 _91854 _91858 _91859.
Proof. exact (@lem3581357 _91854 _91858 _91859). Qed.
Lemma lem3581360 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3581361 {_91854 _91858 _91859 : Type'} : (term50 _91854 _91858 _91859) = (term55 _91854 _91858 _91859).
Proof. exact (@lem3581360 (term51 _91854 _91858 _91859)). Qed.
Lemma lem3581363 (t : Prop) : (term56 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3581364 {_91854 _91858 _91859 : Type'} : (term55 _91854 _91858 _91859) = (term48 _91854 _91858 _91859).
Proof. exact (@lem3581363 (term48 _91854 _91858 _91859)). Qed.
Lemma lem3581401 {_91854 _91858 _91859 : Type'} : (term50 _91854 _91858 _91859) = (term48 _91854 _91858 _91859).
Proof. exact (TRANS (@lem3581361 _91854 _91858 _91859) (@lem3581364 _91854 _91858 _91859)). Qed.
Lemma lem3581406 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term28 _91854 _91858 _91859 P f x g h) = (term28 _91854 _91858 _91859 P f x g h).
Proof. exact (eq_refl (term28 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581407 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term13 _91854 _91858 _91859 P f x g) = (term13 _91854 _91858 _91859 P f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581406 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581408 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581409 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term31 _91854 _91858 _91859 P f x g) = (term31 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581408 _91858) (@lem3581407 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581410 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term33 _91854 _91858 _91859 P f g) = (term33 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581409 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581411 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581412 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term34 _91854 _91858 _91859 P f g) = (term34 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581411 _91859) (@lem3581410 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581413 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : ((g y) = (f x)) = ((g y) = (f x)).
Proof. exact (eq_refl ((g y) = (f x))). Qed.
Lemma lem3581414 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term57 _91854 _91858 _91859 g f x) = (term57 _91854 _91858 _91859 g f x).
Proof. exact (fun_ext (fun y : _91858 => @lem3581413 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3581415 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581416 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term58 _91854 _91858 _91859 g f x) = (term58 _91854 _91858 _91859 g f x).
Proof. exact (MK_COMB (@lem3581415 _91858) (@lem3581414 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581419 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term59 _91859 P x) = (term59 _91859 P x).
Proof. exact (eq_refl (term59 _91859 P x)). Qed.
Lemma lem3581420 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term60 _91854 _91858 _91859 P g f x) = (term60 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3581419 _91859 P x) (@lem3581416 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581421 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term61 _91854 _91858 _91859 P g f) = (term61 _91854 _91858 _91859 P g f).
Proof. exact (fun_ext (fun x : _91859 => @lem3581420 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581422 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581423 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term36 _91854 _91858 _91859 P g f) = (term36 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581422 _91859) (@lem3581421 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581425 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term35 _91854 _91858 _91859 P g f) = (term35 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581424) (@lem3581423 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581426 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term36 _91854 _91858 _91859 P g f) = (term34 _91854 _91858 _91859 P f g)) = ((term36 _91854 _91858 _91859 P g f) = (term34 _91854 _91858 _91859 P f g)).
Proof. exact (MK_COMB (@lem3581425 _91854 _91858 _91859 P g f) (@lem3581412 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581427 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) : (term38 _91854 _91858 _91859 P f) = (term38 _91854 _91858 _91859 P f).
Proof. exact (fun_ext (fun g : _91858 -> _91854 => @lem3581426 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581428 {_91854 _91858 : Type'} : (@all (_91858 -> _91854)) = (@all (_91858 -> _91854)).
Proof. exact (eq_refl (@all (_91858 -> _91854))). Qed.
Lemma lem3581429 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) : (term40 _91854 _91858 _91859 P f) = (term40 _91854 _91858 _91859 P f).
Proof. exact (MK_COMB (@lem3581428 _91854 _91858) (@lem3581427 _91854 _91858 _91859 P f)). Qed.
Lemma lem3581430 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) : (term42 _91854 _91858 _91859 P) = (term42 _91854 _91858 _91859 P).
Proof. exact (fun_ext (fun f : _91859 -> _91854 => @lem3581429 _91854 _91858 _91859 P f)). Qed.
Lemma lem3581431 {_91854 _91859 : Type'} : (@all (_91859 -> _91854)) = (@all (_91859 -> _91854)).
Proof. exact (eq_refl (@all (_91859 -> _91854))). Qed.
Lemma lem3581432 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) : (term44 _91854 _91858 _91859 P) = (term44 _91854 _91858 _91859 P).
Proof. exact (MK_COMB (@lem3581431 _91854 _91859) (@lem3581430 _91854 _91858 _91859 P)). Qed.
Lemma lem3581433 {_91854 _91858 _91859 : Type'} : (term46 _91854 _91858 _91859) = (term46 _91854 _91858 _91859).
Proof. exact (fun_ext (fun P : _91859 -> Prop => @lem3581432 _91854 _91858 _91859 P)). Qed.
Lemma lem3581434 {_91859 : Type'} : (@all (_91859 -> Prop)) = (@all (_91859 -> Prop)).
Proof. exact (eq_refl (@all (_91859 -> Prop))). Qed.
Lemma lem3581435 {_91854 _91858 _91859 : Type'} : (term48 _91854 _91858 _91859) = (term48 _91854 _91858 _91859).
Proof. exact (MK_COMB (@lem3581434 _91859) (@lem3581433 _91854 _91858 _91859)). Qed.
Lemma lem3581484 {_91854 _91858 _91859 : Type'} : (term50 _91854 _91858 _91859) = (term48 _91854 _91858 _91859).
Proof. exact (TRANS (@lem3581401 _91854 _91858 _91859) (@lem3581435 _91854 _91858 _91859)). Qed.
Lemma lem3581485 {_91854 _91858 _91859 : Type'} : (term48 _91854 _91858 _91859) = (term50 _91854 _91858 _91859).
Proof. exact (SYM (@lem3581484 _91854 _91858 _91859)). Qed.
Lemma lem3581487 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3581488 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term36 _91854 _91858 _91859 P g f) = (term34 _91854 _91858 _91859 P f g)) = (term62 _91854 _91858 _91859 P f g).
Proof. exact (@lem3581487 ((term36 _91854 _91858 _91859 P g f) = (term34 _91854 _91858 _91859 P f g))). Qed.
Lemma lem3581489 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term62 _91854 _91858 _91859 P f g) = ((term36 _91854 _91858 _91859 P g f) = (term34 _91854 _91858 _91859 P f g)).
Proof. exact (SYM (@lem3581488 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581490 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h1 : term63 _91854 _91858 _91859 P f g) : term63 _91854 _91858 _91859 P f g.
Proof. exact (h1). Qed.
Lemma lem3581494 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : ((g y) = (f x)) = ((g y) = (f x)).
Proof. exact (eq_refl ((g y) = (f x))). Qed.
Lemma lem3581495 {_91858 : Type'} (P : _91858 -> Prop) : (term64 _91858 P) = (term65 _91858 P).
Proof. exact (@lem18394 _91858 P). Qed.
Lemma lem3581496 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term66 _91854 _91858 _91859 g f x) = (term67 _91854 _91858 _91859 g f x).
Proof. exact (@lem3581495 _91858 (term57 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581497 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : (term68 _91854 _91858 _91859 g f x y) = ((g y) = (f x)).
Proof. exact (eq_refl (term68 _91854 _91858 _91859 g f x y)). Qed.
Lemma lem3581498 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3581500 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : (term69 _91854 _91858 _91859 g f x y) = (term70 _91854 _91858 _91859 g y f x).
Proof. exact (MK_COMB (@lem3581498) (@lem3581497 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3581501 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term71 _91854 _91858 _91859 g f x) = (term72 _91854 _91858 _91859 g f x).
Proof. exact (fun_ext (fun y : _91858 => @lem3581500 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3581502 {_91858 : Type'} : (@all _91858) = (@all _91858).
Proof. exact (eq_refl (@all _91858)). Qed.
Lemma lem3581503 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term67 _91854 _91858 _91859 g f x) = (term73 _91854 _91858 _91859 g f x).
Proof. exact (MK_COMB (@lem3581502 _91858) (@lem3581501 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581504 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term66 _91854 _91858 _91859 g f x) = (term73 _91854 _91858 _91859 g f x).
Proof. exact (TRANS (@lem3581496 _91854 _91858 _91859 g f x) (@lem3581503 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581505 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term57 _91854 _91858 _91859 g f x) = (term57 _91854 _91858 _91859 g f x).
Proof. exact (fun_ext (fun y : _91858 => @lem3581494 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3581506 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581507 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term58 _91854 _91858 _91859 g f x) = (term58 _91854 _91858 _91859 g f x).
Proof. exact (MK_COMB (@lem3581506 _91858) (@lem3581505 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581509 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term74 _91859 P x) = (term74 _91859 P x).
Proof. exact (eq_refl (term74 _91859 P x)). Qed.
Lemma lem3581510 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term75 _91854 _91858 _91859 P g f x) = (term76 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3581509 _91859 P x) (@lem3581504 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581511 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term77 _91854 _91858 _91859 P g f x) = (term75 _91854 _91858 _91859 P g f x).
Proof. exact (@lem17362 (P x) (term58 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581512 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term77 _91854 _91858 _91859 P g f x) = (term76 _91854 _91858 _91859 P g f x).
Proof. exact (TRANS (@lem3581511 _91854 _91858 _91859 P g f x) (@lem3581510 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581514 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term78 _91859 P x) = (term78 _91859 P x).
Proof. exact (eq_refl (term78 _91859 P x)). Qed.
Lemma lem3581515 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term79 _91854 _91858 _91859 P g f x) = (term79 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3581514 _91859 P x) (@lem3581507 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581516 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term60 _91854 _91858 _91859 P g f x) = (term79 _91854 _91858 _91859 P g f x).
Proof. exact (@lem17265 (P x) (term58 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581517 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term60 _91854 _91858 _91859 P g f x) = (term79 _91854 _91858 _91859 P g f x).
Proof. exact (TRANS (@lem3581516 _91854 _91858 _91859 P g f x) (@lem3581515 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581518 {_91859 : Type'} (P : _91859 -> Prop) : (term80 _91859 P) = (term81 _91859 P).
Proof. exact (@lem18392 _91859 P). Qed.
Lemma lem3581519 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term82 _91854 _91858 _91859 P g f) = (term83 _91854 _91858 _91859 P g f).
Proof. exact (@lem3581518 _91859 (term61 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581520 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term84 _91854 _91858 _91859 P g f x) = (term60 _91854 _91858 _91859 P g f x).
Proof. exact (eq_refl (term84 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581521 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3581522 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term85 _91854 _91858 _91859 P g f x) = (term77 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3581521) (@lem3581520 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581523 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term85 _91854 _91858 _91859 P g f x) = (term76 _91854 _91858 _91859 P g f x).
Proof. exact (TRANS (@lem3581522 _91854 _91858 _91859 P g f x) (@lem3581512 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581524 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term86 _91854 _91858 _91859 P g f) = (term87 _91854 _91858 _91859 P g f).
Proof. exact (fun_ext (fun x : _91859 => @lem3581523 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581525 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3581526 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term83 _91854 _91858 _91859 P g f) = (term88 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581525 _91859) (@lem3581524 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581527 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term82 _91854 _91858 _91859 P g f) = (term88 _91854 _91858 _91859 P g f).
Proof. exact (TRANS (@lem3581519 _91854 _91858 _91859 P g f) (@lem3581526 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581528 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term61 _91854 _91858 _91859 P g f) = (term89 _91854 _91858 _91859 P g f).
Proof. exact (fun_ext (fun x : _91859 => @lem3581517 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581529 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581530 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term36 _91854 _91858 _91859 P g f) = (term90 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581529 _91859) (@lem3581528 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581539 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term91 _91854 _91858 _91859 P f x g h) = (term92 _91854 _91858 _91859 P f x g h).
Proof. exact (@lem17362 (P x) ((f x) = (g h))). Qed.
Lemma lem3581544 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term28 _91854 _91858 _91859 P f x g h) = (term93 _91854 _91858 _91859 P f x g h).
Proof. exact (@lem17265 (P x) ((f x) = (g h))). Qed.
Lemma lem3581545 {_91858 : Type'} (P : _91858 -> Prop) : (term64 _91858 P) = (term65 _91858 P).
Proof. exact (@lem18394 _91858 P). Qed.
Lemma lem3581546 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term94 _91854 _91858 _91859 P f x g) = (term95 _91854 _91858 _91859 P f x g).
Proof. exact (@lem3581545 _91858 (term13 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581547 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term27 _91854 _91858 _91859 P f x g h) = (term28 _91854 _91858 _91859 P f x g h).
Proof. exact (eq_refl (term27 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3581549 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term96 _91854 _91858 _91859 P f x g h) = (term91 _91854 _91858 _91859 P f x g h).
Proof. exact (MK_COMB (@lem3581548) (@lem3581547 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581550 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term96 _91854 _91858 _91859 P f x g h) = (term92 _91854 _91858 _91859 P f x g h).
Proof. exact (TRANS (@lem3581549 _91854 _91858 _91859 P f x g h) (@lem3581539 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581551 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term97 _91854 _91858 _91859 P f x g) = (term98 _91854 _91858 _91859 P f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581550 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581552 {_91858 : Type'} : (@all _91858) = (@all _91858).
Proof. exact (eq_refl (@all _91858)). Qed.
Lemma lem3581553 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term95 _91854 _91858 _91859 P f x g) = (term99 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581552 _91858) (@lem3581551 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581554 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term94 _91854 _91858 _91859 P f x g) = (term99 _91854 _91858 _91859 P f x g).
Proof. exact (TRANS (@lem3581546 _91854 _91858 _91859 P f x g) (@lem3581553 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581555 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term13 _91854 _91858 _91859 P f x g) = (term100 _91854 _91858 _91859 P f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581544 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581556 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581557 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term31 _91854 _91858 _91859 P f x g) = (term101 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581556 _91858) (@lem3581555 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581558 {_91859 : Type'} (P : _91859 -> Prop) : (term80 _91859 P) = (term81 _91859 P).
Proof. exact (@lem18392 _91859 P). Qed.
Lemma lem3581559 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term102 _91854 _91858 _91859 P f g) = (term103 _91854 _91858 _91859 P f g).
Proof. exact (@lem3581558 _91859 (term33 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581560 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term104 _91854 _91858 _91859 P f g x) = (term31 _91854 _91858 _91859 P f x g).
Proof. exact (eq_refl (term104 _91854 _91858 _91859 P f g x)). Qed.
Lemma lem3581561 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3581562 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term105 _91854 _91858 _91859 P f g x) = (term94 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581561) (@lem3581560 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581563 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term105 _91854 _91858 _91859 P f g x) = (term99 _91854 _91858 _91859 P f x g).
Proof. exact (TRANS (@lem3581562 _91854 _91858 _91859 P f x g) (@lem3581554 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581564 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term106 _91854 _91858 _91859 P f g) = (term107 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581563 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581565 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3581566 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term103 _91854 _91858 _91859 P f g) = (term108 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581565 _91859) (@lem3581564 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581567 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term102 _91854 _91858 _91859 P f g) = (term108 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3581559 _91854 _91858 _91859 P f g) (@lem3581566 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581568 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term33 _91854 _91858 _91859 P f g) = (term109 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581557 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581569 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581570 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term34 _91854 _91858 _91859 P f g) = (term110 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581569 _91859) (@lem3581568 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3581572 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term111 _91854 _91858 _91859 P g f) = (term112 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581571) (@lem3581527 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581573 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term113 _91854 _91858 _91859 P f g) = (term114 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581572 _91854 _91858 _91859 P g f) (@lem3581570 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3581575 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term115 _91854 _91858 _91859 P g f) = (term116 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581574) (@lem3581530 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581576 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term117 _91854 _91858 _91859 P f g) = (term118 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581575 _91854 _91858 _91859 P g f) (@lem3581567 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3581578 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term119 _91854 _91858 _91859 P f g) = (term120 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581577) (@lem3581576 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581579 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term121 _91854 _91858 _91859 P f g) = (term122 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581578 _91854 _91858 _91859 P f g) (@lem3581573 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581580 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term63 _91854 _91858 _91859 P f g) = (term121 _91854 _91858 _91859 P f g).
Proof. exact (@lem17646 (term36 _91854 _91858 _91859 P g f) (term34 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581581 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term63 _91854 _91858 _91859 P f g) = (term122 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3581580 _91854 _91858 _91859 P f g) (@lem3581579 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581639 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3581640 {_91858 : Type'} (P : _91858 -> Prop) (Q : _91858 -> Prop) : (term123 _91858 P Q) = (term124 _91858 P Q).
Proof. exact (@lem3581639 _91858 P Q). Qed.
Lemma lem3581641 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term125 _91854 _91858 _91859 P f x g) = (term126 _91854 _91858 _91859 P f x g).
Proof. exact (@lem3581640 _91858 (term127 _91858 _91859 P x) (term128 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581642 {_91858 _91859 : Type'} (h : _91858) (P : _91859 -> Prop) (x : _91859) : (term129 _91858 _91859 P x h) = (P x).
Proof. exact (eq_refl (term129 _91858 _91859 P x h)). Qed.
Lemma lem3581643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3581644 {_91858 _91859 : Type'} (h : _91858) (P : _91859 -> Prop) (x : _91859) : (term130 _91858 _91859 P x h) = (term74 _91859 P x).
Proof. exact (MK_COMB (@lem3581643) (@lem3581642 _91858 _91859 h P x)). Qed.
Lemma lem3581645 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term131 _91854 _91858 _91859 f x g h) = (term132 _91854 _91858 _91859 f x g h).
Proof. exact (eq_refl (term131 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581646 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term133 _91854 _91858 _91859 P f x g h) = (term92 _91854 _91858 _91859 P f x g h).
Proof. exact (MK_COMB (@lem3581644 _91858 _91859 h P x) (@lem3581645 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581647 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term134 _91854 _91858 _91859 P f x g) = (term98 _91854 _91858 _91859 P f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581646 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581648 {_91858 : Type'} : (@all _91858) = (@all _91858).
Proof. exact (eq_refl (@all _91858)). Qed.
Lemma lem3581649 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term125 _91854 _91858 _91859 P f x g) = (term99 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581648 _91858) (@lem3581647 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581651 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term135 _91854 _91858 _91859 P f x g) = (term136 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581650) (@lem3581649 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581652 {_91858 _91859 : Type'} (h : _91858) (P : _91859 -> Prop) (x : _91859) : (term129 _91858 _91859 P x h) = (P x).
Proof. exact (eq_refl (term129 _91858 _91859 P x h)). Qed.
Lemma lem3581653 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term137 _91858 _91859 P x) = (term127 _91858 _91859 P x).
Proof. exact (fun_ext (fun h : _91858 => @lem3581652 _91858 _91859 h P x)). Qed.
Lemma lem3581654 {_91858 : Type'} : (@all _91858) = (@all _91858).
Proof. exact (eq_refl (@all _91858)). Qed.
Lemma lem3581655 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term138 _91858 _91859 P x) = (term139 _91858 _91859 P x).
Proof. exact (MK_COMB (@lem3581654 _91858) (@lem3581653 _91858 _91859 P x)). Qed.
Lemma lem3581656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3581657 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term140 _91858 _91859 P x) = (term141 _91858 _91859 P x).
Proof. exact (MK_COMB (@lem3581656) (@lem3581655 _91858 _91859 P x)). Qed.
Lemma lem3581658 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term131 _91854 _91858 _91859 f x g h) = (term132 _91854 _91858 _91859 f x g h).
Proof. exact (eq_refl (term131 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581659 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term142 _91854 _91858 _91859 f x g) = (term128 _91854 _91858 _91859 f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581658 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581660 {_91858 : Type'} : (@all _91858) = (@all _91858).
Proof. exact (eq_refl (@all _91858)). Qed.
Lemma lem3581661 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term143 _91854 _91858 _91859 f x g) = (term144 _91854 _91858 _91859 f x g).
Proof. exact (MK_COMB (@lem3581660 _91858) (@lem3581659 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581662 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term126 _91854 _91858 _91859 P f x g) = (term145 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581657 _91858 _91859 P x) (@lem3581661 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581663 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : ((term125 _91854 _91858 _91859 P f x g) = (term126 _91854 _91858 _91859 P f x g)) = ((term99 _91854 _91858 _91859 P f x g) = (term145 _91854 _91858 _91859 P f x g)).
Proof. exact (MK_COMB (@lem3581651 _91854 _91858 _91859 P f x g) (@lem3581662 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581664 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term99 _91854 _91858 _91859 P f x g) = (term145 _91854 _91858 _91859 P f x g).
Proof. exact (EQ_MP (@lem3581663 _91854 _91858 _91859 P f x g) (@lem3581641 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581666 {A : Type'} (t : Prop) : (term146 A t) = t.
Proof. exact (EQ_MP (@lem18935 A t) (@lem18934 A t)). Qed.
Lemma lem3581667 {_91858 : Type'} (t : Prop) : (term146 _91858 t) = t.
Proof. exact (@lem3581666 _91858 t). Qed.
Lemma lem3581668 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term139 _91858 _91859 P x) = (P x).
Proof. exact (@lem3581667 _91858 (P x)). Qed.
Lemma lem3581669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3581670 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term141 _91858 _91859 P x) = (term74 _91859 P x).
Proof. exact (MK_COMB (@lem3581669) (@lem3581668 _91858 _91859 P x)). Qed.
Lemma lem3581675 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term144 _91854 _91858 _91859 f x g) = (term144 _91854 _91858 _91859 f x g).
Proof. exact (eq_refl (term144 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581676 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term145 _91854 _91858 _91859 P f x g) = (term147 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581670 _91858 _91859 P x) (@lem3581675 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581677 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term99 _91854 _91858 _91859 P f x g) = (term147 _91854 _91858 _91859 P f x g).
Proof. exact (TRANS (@lem3581664 _91854 _91858 _91859 P f x g) (@lem3581676 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581678 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term107 _91854 _91858 _91859 P f g) = (term148 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581677 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581679 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3581680 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term108 _91854 _91858 _91859 P f g) = (term149 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581679 _91859) (@lem3581678 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581709 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term116 _91854 _91858 _91859 P g f) = (term116 _91854 _91858 _91859 P g f).
Proof. exact (eq_refl (term116 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581710 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term118 _91854 _91858 _91859 P f g) = (term150 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581709 _91854 _91858 _91859 P g f) (@lem3581680 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3581712 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term120 _91854 _91858 _91859 P f g) = (term151 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581711) (@lem3581710 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581750 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3581751 {_91858 : Type'} (P : _91858 -> Prop) (Q : _91858 -> Prop) : (term152 _91858 P Q) = (term153 _91858 P Q).
Proof. exact (@lem3581750 _91858 P Q). Qed.
Lemma lem3581752 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term154 _91854 _91858 _91859 P f x g) = (term155 _91854 _91858 _91859 P f x g).
Proof. exact (@lem3581751 _91858 (term156 _91858 _91859 P x) (term157 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581753 {_91858 _91859 : Type'} (h : _91858) (P : _91859 -> Prop) (x : _91859) : (term158 _91858 _91859 P x h) = (term159 _91859 P x).
Proof. exact (eq_refl (term158 _91858 _91859 P x h)). Qed.
Lemma lem3581754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3581755 {_91858 _91859 : Type'} (h : _91858) (P : _91859 -> Prop) (x : _91859) : (term160 _91858 _91859 P x h) = (term78 _91859 P x).
Proof. exact (MK_COMB (@lem3581754) (@lem3581753 _91858 _91859 h P x)). Qed.
Lemma lem3581756 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term161 _91854 _91858 _91859 f x g h) = ((f x) = (g h)).
Proof. exact (eq_refl (term161 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581757 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term162 _91854 _91858 _91859 P f x g h) = (term93 _91854 _91858 _91859 P f x g h).
Proof. exact (MK_COMB (@lem3581755 _91858 _91859 h P x) (@lem3581756 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581758 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term163 _91854 _91858 _91859 P f x g) = (term100 _91854 _91858 _91859 P f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581757 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581759 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581760 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term154 _91854 _91858 _91859 P f x g) = (term101 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581759 _91858) (@lem3581758 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581762 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term164 _91854 _91858 _91859 P f x g) = (term165 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581761) (@lem3581760 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581763 {_91858 _91859 : Type'} (h : _91858) (P : _91859 -> Prop) (x : _91859) : (term158 _91858 _91859 P x h) = (term159 _91859 P x).
Proof. exact (eq_refl (term158 _91858 _91859 P x h)). Qed.
Lemma lem3581764 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term166 _91858 _91859 P x) = (term156 _91858 _91859 P x).
Proof. exact (fun_ext (fun h : _91858 => @lem3581763 _91858 _91859 h P x)). Qed.
Lemma lem3581765 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581766 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term167 _91858 _91859 P x) = (term168 _91858 _91859 P x).
Proof. exact (MK_COMB (@lem3581765 _91858) (@lem3581764 _91858 _91859 P x)). Qed.
Lemma lem3581767 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3581768 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term169 _91858 _91859 P x) = (term170 _91858 _91859 P x).
Proof. exact (MK_COMB (@lem3581767) (@lem3581766 _91858 _91859 P x)). Qed.
Lemma lem3581769 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term161 _91854 _91858 _91859 f x g h) = ((f x) = (g h)).
Proof. exact (eq_refl (term161 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581770 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term171 _91854 _91858 _91859 f x g) = (term157 _91854 _91858 _91859 f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581769 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581771 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581772 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term172 _91854 _91858 _91859 f x g) = (term173 _91854 _91858 _91859 f x g).
Proof. exact (MK_COMB (@lem3581771 _91858) (@lem3581770 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581773 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term155 _91854 _91858 _91859 P f x g) = (term174 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581768 _91858 _91859 P x) (@lem3581772 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581774 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : ((term154 _91854 _91858 _91859 P f x g) = (term155 _91854 _91858 _91859 P f x g)) = ((term101 _91854 _91858 _91859 P f x g) = (term174 _91854 _91858 _91859 P f x g)).
Proof. exact (MK_COMB (@lem3581762 _91854 _91858 _91859 P f x g) (@lem3581773 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581775 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term101 _91854 _91858 _91859 P f x g) = (term174 _91854 _91858 _91859 P f x g).
Proof. exact (EQ_MP (@lem3581774 _91854 _91858 _91859 P f x g) (@lem3581752 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581777 {A : Type'} (t : Prop) : (term175 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem3581778 {_91858 : Type'} (t : Prop) : (term175 _91858 t) = t.
Proof. exact (@lem3581777 _91858 t). Qed.
Lemma lem3581779 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term168 _91858 _91859 P x) = (term159 _91859 P x).
Proof. exact (@lem3581778 _91858 (term159 _91859 P x)). Qed.
Lemma lem3581780 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3581781 {_91858 _91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term170 _91858 _91859 P x) = (term78 _91859 P x).
Proof. exact (MK_COMB (@lem3581780) (@lem3581779 _91858 _91859 P x)). Qed.
Lemma lem3581786 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term173 _91854 _91858 _91859 f x g) = (term173 _91854 _91858 _91859 f x g).
Proof. exact (eq_refl (term173 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581787 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term174 _91854 _91858 _91859 P f x g) = (term176 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581781 _91858 _91859 P x) (@lem3581786 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581788 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term101 _91854 _91858 _91859 P f x g) = (term176 _91854 _91858 _91859 P f x g).
Proof. exact (TRANS (@lem3581775 _91854 _91858 _91859 P f x g) (@lem3581787 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581789 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term109 _91854 _91858 _91859 P f g) = (term177 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581788 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581790 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581791 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term110 _91854 _91858 _91859 P f g) = (term178 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581790 _91859) (@lem3581789 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581840 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term112 _91854 _91858 _91859 P g f) = (term112 _91854 _91858 _91859 P g f).
Proof. exact (eq_refl (term112 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581841 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term114 _91854 _91858 _91859 P f g) = (term179 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581840 _91854 _91858 _91859 P g f) (@lem3581791 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581842 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term122 _91854 _91858 _91859 P f g) = (term180 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581712 _91854 _91858 _91859 P f g) (@lem3581841 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581844 {A : Type'} (P : Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3581845 {_91858 : Type'} (P : Prop) (Q : _91858 -> Prop) : (term181 _91858 P Q) = (term182 _91858 P Q).
Proof. exact (@lem3581844 _91858 P Q). Qed.
Lemma lem3581846 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term183 _91854 _91858 _91859 P g f x) = (term184 _91854 _91858 _91859 P g f x).
Proof. exact (@lem3581845 _91858 (term159 _91859 P x) (term57 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581847 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : (term68 _91854 _91858 _91859 g f x y) = ((g y) = (f x)).
Proof. exact (eq_refl (term68 _91854 _91858 _91859 g f x y)). Qed.
Lemma lem3581848 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term185 _91854 _91858 _91859 g f x) = (term57 _91854 _91858 _91859 g f x).
Proof. exact (fun_ext (fun y : _91858 => @lem3581847 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3581849 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581850 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term186 _91854 _91858 _91859 g f x) = (term58 _91854 _91858 _91859 g f x).
Proof. exact (MK_COMB (@lem3581849 _91858) (@lem3581848 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581851 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term78 _91859 P x) = (term78 _91859 P x).
Proof. exact (eq_refl (term78 _91859 P x)). Qed.
Lemma lem3581852 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term183 _91854 _91858 _91859 P g f x) = (term79 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3581851 _91859 P x) (@lem3581850 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3581853 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581854 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term187 _91854 _91858 _91859 P g f x) = (term188 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3581853) (@lem3581852 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581855 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : (term68 _91854 _91858 _91859 g f x y) = ((g y) = (f x)).
Proof. exact (eq_refl (term68 _91854 _91858 _91859 g f x y)). Qed.
Lemma lem3581856 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term78 _91859 P x) = (term78 _91859 P x).
Proof. exact (eq_refl (term78 _91859 P x)). Qed.
Lemma lem3581857 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : (term189 _91854 _91858 _91859 P g f x y) = (term190 _91854 _91858 _91859 P g y f x).
Proof. exact (MK_COMB (@lem3581856 _91859 P x) (@lem3581855 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3581858 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term191 _91854 _91858 _91859 P g f x) = (term192 _91854 _91858 _91859 P g f x).
Proof. exact (fun_ext (fun y : _91858 => @lem3581857 _91854 _91858 _91859 P g y f x)). Qed.
Lemma lem3581859 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581860 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term184 _91854 _91858 _91859 P g f x) = (term193 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3581859 _91858) (@lem3581858 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581861 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : ((term183 _91854 _91858 _91859 P g f x) = (term184 _91854 _91858 _91859 P g f x)) = ((term79 _91854 _91858 _91859 P g f x) = (term193 _91854 _91858 _91859 P g f x)).
Proof. exact (MK_COMB (@lem3581854 _91854 _91858 _91859 P g f x) (@lem3581860 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581862 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term79 _91854 _91858 _91859 P g f x) = (term193 _91854 _91858 _91859 P g f x).
Proof. exact (EQ_MP (@lem3581861 _91854 _91858 _91859 P g f x) (@lem3581846 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581863 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term89 _91854 _91858 _91859 P g f) = (term194 _91854 _91858 _91859 P g f).
Proof. exact (fun_ext (fun x : _91859 => @lem3581862 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581864 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581865 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term90 _91854 _91858 _91859 P g f) = (term195 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581864 _91859) (@lem3581863 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581867 {A B : Type'} (P : type1413 A B) : (term0 A B P) = (term1 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3581868 {_91858 _91859 : Type'} (P : type1470 _91858 _91859) : (term8 _91858 _91859 P) = (term7 _91858 _91859 P).
Proof. exact (@lem3581867 _91859 _91858 P). Qed.
Lemma lem3581869 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term196 _91854 _91858 _91859 P g f) = (term197 _91854 _91858 _91859 P g f).
Proof. exact (@lem3581868 _91858 _91859 (term198 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581870 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term199 _91854 _91858 _91859 P g f x) = (term192 _91854 _91858 _91859 P g f x).
Proof. exact (eq_refl (term199 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581871 {_91858 : Type'} (y : _91858) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3581872 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) (y : _91858) : (term200 _91854 _91858 _91859 P g f x y) = (term201 _91854 _91858 _91859 P g f x y).
Proof. exact (MK_COMB (@lem3581870 _91854 _91858 _91859 P g f x) (@lem3581871 _91858 y)). Qed.
Lemma lem3581873 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : (term201 _91854 _91858 _91859 P g f x y) = (term190 _91854 _91858 _91859 P g y f x).
Proof. exact (eq_refl (term201 _91854 _91858 _91859 P g f x y)). Qed.
Lemma lem3581874 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : (term200 _91854 _91858 _91859 P g f x y) = (term190 _91854 _91858 _91859 P g y f x).
Proof. exact (TRANS (@lem3581872 _91854 _91858 _91859 P g f x y) (@lem3581873 _91854 _91858 _91859 P g y f x)). Qed.
Lemma lem3581875 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term202 _91854 _91858 _91859 P g f x) = (term192 _91854 _91858 _91859 P g f x).
Proof. exact (fun_ext (fun y : _91858 => @lem3581874 _91854 _91858 _91859 P g y f x)). Qed.
Lemma lem3581876 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581877 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term203 _91854 _91858 _91859 P g f x) = (term193 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3581876 _91858) (@lem3581875 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581878 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term204 _91854 _91858 _91859 P g f) = (term194 _91854 _91858 _91859 P g f).
Proof. exact (fun_ext (fun x : _91859 => @lem3581877 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581879 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581880 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term196 _91854 _91858 _91859 P g f) = (term195 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581879 _91859) (@lem3581878 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581882 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term205 _91854 _91858 _91859 P g f) = (term206 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581881) (@lem3581880 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581883 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term199 _91854 _91858 _91859 P g f x) = (term192 _91854 _91858 _91859 P g f x).
Proof. exact (eq_refl (term199 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3581884 {_91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem3581885 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (y : _91859 -> _91858) (x : _91859) : (term207 _91854 _91858 _91859 P g f y x) = (term208 _91854 _91858 _91859 P g f y x).
Proof. exact (MK_COMB (@lem3581883 _91854 _91858 _91859 P g f x) (@lem3581884 _91858 _91859 y x)). Qed.
Lemma lem3581886 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (x : _91859) : (term208 _91854 _91858 _91859 P g f y x) = (term209 _91854 _91858 _91859 P g y f x).
Proof. exact (eq_refl (term208 _91854 _91858 _91859 P g f y x)). Qed.
Lemma lem3581887 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (x : _91859) : (term207 _91854 _91858 _91859 P g f y x) = (term209 _91854 _91858 _91859 P g y f x).
Proof. exact (TRANS (@lem3581885 _91854 _91858 _91859 P g f y x) (@lem3581886 _91854 _91858 _91859 P g y f x)). Qed.
Lemma lem3581888 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term210 _91854 _91858 _91859 P g f y) = (term211 _91854 _91858 _91859 P g y f).
Proof. exact (fun_ext (fun x : _91859 => @lem3581887 _91854 _91858 _91859 P g y f x)). Qed.
Lemma lem3581889 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581890 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term212 _91854 _91858 _91859 P g f y) = (term213 _91854 _91858 _91859 P g y f).
Proof. exact (MK_COMB (@lem3581889 _91859) (@lem3581888 _91854 _91858 _91859 P g y f)). Qed.
Lemma lem3581891 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term214 _91854 _91858 _91859 P g f) = (term215 _91854 _91858 _91859 P g f).
Proof. exact (fun_ext (fun y : _91859 -> _91858 => @lem3581890 _91854 _91858 _91859 P g y f)). Qed.
Lemma lem3581892 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3581893 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term197 _91854 _91858 _91859 P g f) = (term216 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581892 _91858 _91859) (@lem3581891 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581894 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : ((term196 _91854 _91858 _91859 P g f) = (term197 _91854 _91858 _91859 P g f)) = ((term195 _91854 _91858 _91859 P g f) = (term216 _91854 _91858 _91859 P g f)).
Proof. exact (MK_COMB (@lem3581882 _91854 _91858 _91859 P g f) (@lem3581893 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581895 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term195 _91854 _91858 _91859 P g f) = (term216 _91854 _91858 _91859 P g f).
Proof. exact (EQ_MP (@lem3581894 _91854 _91858 _91859 P g f) (@lem3581869 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581896 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term90 _91854 _91858 _91859 P g f) = (term216 _91854 _91858 _91859 P g f).
Proof. exact (TRANS (@lem3581865 _91854 _91858 _91859 P g f) (@lem3581895 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3581898 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term116 _91854 _91858 _91859 P g f) = (term217 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581897) (@lem3581896 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581899 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term149 _91854 _91858 _91859 P f g) = (term149 _91854 _91858 _91859 P f g).
Proof. exact (eq_refl (term149 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581900 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term150 _91854 _91858 _91859 P f g) = (term218 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581898 _91854 _91858 _91859 P g f) (@lem3581899 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581902 {A : Type'} (P : A -> Prop) (Q : Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3581903 {_91858 _91859 : Type'} (P : type805 _91858 _91859) (Q : Prop) : (term221 _91858 _91859 P Q) = (term222 _91858 _91859 P Q).
Proof. exact (@lem3581902 (_91859 -> _91858) P Q). Qed.
Lemma lem3581904 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term223 _91854 _91858 _91859 P f g) = (term224 _91854 _91858 _91859 P f g).
Proof. exact (@lem3581903 _91858 _91859 (term215 _91854 _91858 _91859 P g f) (term149 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581905 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term225 _91854 _91858 _91859 P g f y) = (term213 _91854 _91858 _91859 P g y f).
Proof. exact (eq_refl (term225 _91854 _91858 _91859 P g f y)). Qed.
Lemma lem3581906 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term226 _91854 _91858 _91859 P g f) = (term215 _91854 _91858 _91859 P g f).
Proof. exact (fun_ext (fun y : _91859 -> _91858 => @lem3581905 _91854 _91858 _91859 P g y f)). Qed.
Lemma lem3581907 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3581908 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term227 _91854 _91858 _91859 P g f) = (term216 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581907 _91858 _91859) (@lem3581906 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3581910 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term228 _91854 _91858 _91859 P g f) = (term217 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3581909) (@lem3581908 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3581911 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term149 _91854 _91858 _91859 P f g) = (term149 _91854 _91858 _91859 P f g).
Proof. exact (eq_refl (term149 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581912 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term223 _91854 _91858 _91859 P f g) = (term218 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581910 _91854 _91858 _91859 P g f) (@lem3581911 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581914 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term229 _91854 _91858 _91859 P f g) = (term230 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581913) (@lem3581912 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581915 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term225 _91854 _91858 _91859 P g f y) = (term213 _91854 _91858 _91859 P g y f).
Proof. exact (eq_refl (term225 _91854 _91858 _91859 P g f y)). Qed.
Lemma lem3581916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3581917 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term231 _91854 _91858 _91859 P g f y) = (term232 _91854 _91858 _91859 P g y f).
Proof. exact (MK_COMB (@lem3581916) (@lem3581915 _91854 _91858 _91859 P g y f)). Qed.
Lemma lem3581918 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term149 _91854 _91858 _91859 P f g) = (term149 _91854 _91858 _91859 P f g).
Proof. exact (eq_refl (term149 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581919 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term233 _91854 _91858 _91859 y P f g) = (term234 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3581917 _91854 _91858 _91859 P g y f) (@lem3581918 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581920 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term235 _91854 _91858 _91859 P f g) = (term236 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun y : _91859 -> _91858 => @lem3581919 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3581921 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3581922 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term224 _91854 _91858 _91859 P f g) = (term237 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581921 _91858 _91859) (@lem3581920 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581923 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term223 _91854 _91858 _91859 P f g) = (term224 _91854 _91858 _91859 P f g)) = ((term218 _91854 _91858 _91859 P f g) = (term237 _91854 _91858 _91859 P f g)).
Proof. exact (MK_COMB (@lem3581914 _91854 _91858 _91859 P f g) (@lem3581922 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581924 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term218 _91854 _91858 _91859 P f g) = (term237 _91854 _91858 _91859 P f g).
Proof. exact (EQ_MP (@lem3581923 _91854 _91858 _91859 P f g) (@lem3581904 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581926 {A : Type'} (P : Prop) (Q : A -> Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3581927 {_91859 : Type'} (P : Prop) (Q : _91859 -> Prop) : (term238 _91859 P Q) = (term239 _91859 P Q).
Proof. exact (@lem3581926 _91859 P Q). Qed.
Lemma lem3581928 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term240 _91854 _91858 _91859 y P f g) = (term241 _91854 _91858 _91859 y P f g).
Proof. exact (@lem3581927 _91859 (term213 _91854 _91858 _91859 P g y f) (term148 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581929 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term242 _91854 _91858 _91859 P f g x) = (term147 _91854 _91858 _91859 P f x g).
Proof. exact (eq_refl (term242 _91854 _91858 _91859 P f g x)). Qed.
Lemma lem3581930 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term243 _91854 _91858 _91859 P f g) = (term148 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581929 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581931 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3581932 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term244 _91854 _91858 _91859 P f g) = (term149 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581931 _91859) (@lem3581930 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581933 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term232 _91854 _91858 _91859 P g y f) = (term232 _91854 _91858 _91859 P g y f).
Proof. exact (eq_refl (term232 _91854 _91858 _91859 P g y f)). Qed.
Lemma lem3581934 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term240 _91854 _91858 _91859 y P f g) = (term234 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3581933 _91854 _91858 _91859 P g y f) (@lem3581932 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581936 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term245 _91854 _91858 _91859 y P f g) = (term246 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3581935) (@lem3581934 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3581937 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term242 _91854 _91858 _91859 P f g x) = (term147 _91854 _91858 _91859 P f x g).
Proof. exact (eq_refl (term242 _91854 _91858 _91859 P f g x)). Qed.
Lemma lem3581938 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term232 _91854 _91858 _91859 P g y f) = (term232 _91854 _91858 _91859 P g y f).
Proof. exact (eq_refl (term232 _91854 _91858 _91859 P g y f)). Qed.
Lemma lem3581939 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term247 _91854 _91858 _91859 y P f g x) = (term248 _91854 _91858 _91859 y P f x g).
Proof. exact (MK_COMB (@lem3581938 _91854 _91858 _91859 P g y f) (@lem3581937 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581940 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term249 _91854 _91858 _91859 y P f g) = (term250 _91854 _91858 _91859 y P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581939 _91854 _91858 _91859 y P f x g)). Qed.
Lemma lem3581941 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3581942 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term241 _91854 _91858 _91859 y P f g) = (term251 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3581941 _91859) (@lem3581940 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3581943 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term240 _91854 _91858 _91859 y P f g) = (term241 _91854 _91858 _91859 y P f g)) = ((term234 _91854 _91858 _91859 y P f g) = (term251 _91854 _91858 _91859 y P f g)).
Proof. exact (MK_COMB (@lem3581936 _91854 _91858 _91859 y P f g) (@lem3581942 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3581944 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term234 _91854 _91858 _91859 y P f g) = (term251 _91854 _91858 _91859 y P f g).
Proof. exact (EQ_MP (@lem3581943 _91854 _91858 _91859 y P f g) (@lem3581928 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3581945 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term236 _91854 _91858 _91859 P f g) = (term252 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun y : _91859 -> _91858 => @lem3581944 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3581946 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3581947 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term237 _91854 _91858 _91859 P f g) = (term253 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581946 _91858 _91859) (@lem3581945 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581948 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term218 _91854 _91858 _91859 P f g) = (term253 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3581924 _91854 _91858 _91859 P f g) (@lem3581947 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581949 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term150 _91854 _91858 _91859 P f g) = (term253 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3581900 _91854 _91858 _91859 P f g) (@lem3581948 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3581951 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term151 _91854 _91858 _91859 P f g) = (term254 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581950) (@lem3581949 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581953 {A : Type'} (P : Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3581954 {_91858 : Type'} (P : Prop) (Q : _91858 -> Prop) : (term181 _91858 P Q) = (term182 _91858 P Q).
Proof. exact (@lem3581953 _91858 P Q). Qed.
Lemma lem3581955 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term255 _91854 _91858 _91859 P f x g) = (term256 _91854 _91858 _91859 P f x g).
Proof. exact (@lem3581954 _91858 (term159 _91859 P x) (term157 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581956 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term161 _91854 _91858 _91859 f x g h) = ((f x) = (g h)).
Proof. exact (eq_refl (term161 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581957 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term171 _91854 _91858 _91859 f x g) = (term157 _91854 _91858 _91859 f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581956 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581958 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581959 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term172 _91854 _91858 _91859 f x g) = (term173 _91854 _91858 _91859 f x g).
Proof. exact (MK_COMB (@lem3581958 _91858) (@lem3581957 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581960 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term78 _91859 P x) = (term78 _91859 P x).
Proof. exact (eq_refl (term78 _91859 P x)). Qed.
Lemma lem3581961 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term255 _91854 _91858 _91859 P f x g) = (term176 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581960 _91859 P x) (@lem3581959 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3581962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581963 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term257 _91854 _91858 _91859 P f x g) = (term258 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581962) (@lem3581961 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581964 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term161 _91854 _91858 _91859 f x g h) = ((f x) = (g h)).
Proof. exact (eq_refl (term161 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581965 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term78 _91859 P x) = (term78 _91859 P x).
Proof. exact (eq_refl (term78 _91859 P x)). Qed.
Lemma lem3581966 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term259 _91854 _91858 _91859 P f x g h) = (term93 _91854 _91858 _91859 P f x g h).
Proof. exact (MK_COMB (@lem3581965 _91859 P x) (@lem3581964 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3581967 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term260 _91854 _91858 _91859 P f x g) = (term100 _91854 _91858 _91859 P f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581966 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581968 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581969 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term256 _91854 _91858 _91859 P f x g) = (term101 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581968 _91858) (@lem3581967 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581970 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : ((term255 _91854 _91858 _91859 P f x g) = (term256 _91854 _91858 _91859 P f x g)) = ((term176 _91854 _91858 _91859 P f x g) = (term101 _91854 _91858 _91859 P f x g)).
Proof. exact (MK_COMB (@lem3581963 _91854 _91858 _91859 P f x g) (@lem3581969 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581971 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term176 _91854 _91858 _91859 P f x g) = (term101 _91854 _91858 _91859 P f x g).
Proof. exact (EQ_MP (@lem3581970 _91854 _91858 _91859 P f x g) (@lem3581955 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581972 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term177 _91854 _91858 _91859 P f g) = (term109 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581971 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581973 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581974 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term178 _91854 _91858 _91859 P f g) = (term110 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581973 _91859) (@lem3581972 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581976 {A B : Type'} (P : type1413 A B) : (term0 A B P) = (term1 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3581977 {_91858 _91859 : Type'} (P : type1470 _91858 _91859) : (term8 _91858 _91859 P) = (term7 _91858 _91859 P).
Proof. exact (@lem3581976 _91859 _91858 P). Qed.
Lemma lem3581978 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term261 _91854 _91858 _91859 P f g) = (term262 _91854 _91858 _91859 P f g).
Proof. exact (@lem3581977 _91858 _91859 (term263 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581979 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term264 _91854 _91858 _91859 P f g x) = (term100 _91854 _91858 _91859 P f x g).
Proof. exact (eq_refl (term264 _91854 _91858 _91859 P f g x)). Qed.
Lemma lem3581980 {_91858 : Type'} (h : _91858) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem3581981 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term265 _91854 _91858 _91859 P f g x h) = (term266 _91854 _91858 _91859 P f x g h).
Proof. exact (MK_COMB (@lem3581979 _91854 _91858 _91859 P f x g) (@lem3581980 _91858 h)). Qed.
Lemma lem3581982 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term266 _91854 _91858 _91859 P f x g h) = (term93 _91854 _91858 _91859 P f x g h).
Proof. exact (eq_refl (term266 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581983 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term265 _91854 _91858 _91859 P f g x h) = (term93 _91854 _91858 _91859 P f x g h).
Proof. exact (TRANS (@lem3581981 _91854 _91858 _91859 P f x g h) (@lem3581982 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581984 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term267 _91854 _91858 _91859 P f g x) = (term100 _91854 _91858 _91859 P f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3581983 _91854 _91858 _91859 P f x g h)). Qed.
Lemma lem3581985 {_91858 : Type'} : (@ex _91858) = (@ex _91858).
Proof. exact (eq_refl (@ex _91858)). Qed.
Lemma lem3581986 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term268 _91854 _91858 _91859 P f g x) = (term101 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3581985 _91858) (@lem3581984 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581987 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term269 _91854 _91858 _91859 P f g) = (term109 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3581986 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3581988 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581989 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term261 _91854 _91858 _91859 P f g) = (term110 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581988 _91859) (@lem3581987 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3581991 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term270 _91854 _91858 _91859 P f g) = (term271 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581990) (@lem3581989 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3581992 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term264 _91854 _91858 _91859 P f g x) = (term100 _91854 _91858 _91859 P f x g).
Proof. exact (eq_refl (term264 _91854 _91858 _91859 P f g x)). Qed.
Lemma lem3581993 {_91858 _91859 : Type'} (h : _91859 -> _91858) (x : _91859) : (h x) = (h x).
Proof. exact (eq_refl (h x)). Qed.
Lemma lem3581994 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (x : _91859) : (term272 _91854 _91858 _91859 P f g h x) = (term273 _91854 _91858 _91859 P f g h x).
Proof. exact (MK_COMB (@lem3581992 _91854 _91858 _91859 P f x g) (@lem3581993 _91858 _91859 h x)). Qed.
Lemma lem3581995 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (x : _91859) : (term273 _91854 _91858 _91859 P f g h x) = (term274 _91854 _91858 _91859 P f g h x).
Proof. exact (eq_refl (term273 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3581996 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (x : _91859) : (term272 _91854 _91858 _91859 P f g h x) = (term274 _91854 _91858 _91859 P f g h x).
Proof. exact (TRANS (@lem3581994 _91854 _91858 _91859 P f g h x) (@lem3581995 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3581997 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term275 _91854 _91858 _91859 P f g h) = (term276 _91854 _91858 _91859 P f g h).
Proof. exact (fun_ext (fun x : _91859 => @lem3581996 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3581998 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3581999 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term277 _91854 _91858 _91859 P f g h) = (term278 _91854 _91858 _91859 P f g h).
Proof. exact (MK_COMB (@lem3581998 _91859) (@lem3581997 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3582000 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term279 _91854 _91858 _91859 P f g) = (term280 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun h : _91859 -> _91858 => @lem3581999 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3582001 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3582002 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term262 _91854 _91858 _91859 P f g) = (term281 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582001 _91858 _91859) (@lem3582000 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582003 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term261 _91854 _91858 _91859 P f g) = (term262 _91854 _91858 _91859 P f g)) = ((term110 _91854 _91858 _91859 P f g) = (term281 _91854 _91858 _91859 P f g)).
Proof. exact (MK_COMB (@lem3581991 _91854 _91858 _91859 P f g) (@lem3582002 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582004 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term110 _91854 _91858 _91859 P f g) = (term281 _91854 _91858 _91859 P f g).
Proof. exact (EQ_MP (@lem3582003 _91854 _91858 _91859 P f g) (@lem3581978 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582005 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term178 _91854 _91858 _91859 P f g) = (term281 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3581974 _91854 _91858 _91859 P f g) (@lem3582004 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582006 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term112 _91854 _91858 _91859 P g f) = (term112 _91854 _91858 _91859 P g f).
Proof. exact (eq_refl (term112 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3582007 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term179 _91854 _91858 _91859 P f g) = (term282 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582006 _91854 _91858 _91859 P g f) (@lem3582005 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582009 {A : Type'} (P : A -> Prop) (Q : Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3582010 {_91859 : Type'} (P : _91859 -> Prop) (Q : Prop) : (term219 _91859 P Q) = (term220 _91859 P Q).
Proof. exact (@lem3582009 _91859 P Q). Qed.
Lemma lem3582011 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term283 _91854 _91858 _91859 P f g) = (term284 _91854 _91858 _91859 P f g).
Proof. exact (@lem3582010 _91859 (term87 _91854 _91858 _91859 P g f) (term281 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582012 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term285 _91854 _91858 _91859 P g f x) = (term76 _91854 _91858 _91859 P g f x).
Proof. exact (eq_refl (term285 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3582013 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term286 _91854 _91858 _91859 P g f) = (term87 _91854 _91858 _91859 P g f).
Proof. exact (fun_ext (fun x : _91859 => @lem3582012 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3582014 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3582015 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term287 _91854 _91858 _91859 P g f) = (term88 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3582014 _91859) (@lem3582013 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3582016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3582017 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) : (term288 _91854 _91858 _91859 P g f) = (term112 _91854 _91858 _91859 P g f).
Proof. exact (MK_COMB (@lem3582016) (@lem3582015 _91854 _91858 _91859 P g f)). Qed.
Lemma lem3582018 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term281 _91854 _91858 _91859 P f g) = (term281 _91854 _91858 _91859 P f g).
Proof. exact (eq_refl (term281 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582019 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term283 _91854 _91858 _91859 P f g) = (term282 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582017 _91854 _91858 _91859 P g f) (@lem3582018 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582021 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term289 _91854 _91858 _91859 P f g) = (term290 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582020) (@lem3582019 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582022 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term285 _91854 _91858 _91859 P g f x) = (term76 _91854 _91858 _91859 P g f x).
Proof. exact (eq_refl (term285 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3582023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3582024 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term291 _91854 _91858 _91859 P g f x) = (term292 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3582023) (@lem3582022 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3582025 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term281 _91854 _91858 _91859 P f g) = (term281 _91854 _91858 _91859 P f g).
Proof. exact (eq_refl (term281 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582026 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term293 _91854 _91858 _91859 x P f g) = (term294 _91854 _91858 _91859 x P f g).
Proof. exact (MK_COMB (@lem3582024 _91854 _91858 _91859 P g f x) (@lem3582025 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582027 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term295 _91854 _91858 _91859 P f g) = (term296 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3582026 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582028 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3582029 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term284 _91854 _91858 _91859 P f g) = (term297 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582028 _91859) (@lem3582027 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582030 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term283 _91854 _91858 _91859 P f g) = (term284 _91854 _91858 _91859 P f g)) = ((term282 _91854 _91858 _91859 P f g) = (term297 _91854 _91858 _91859 P f g)).
Proof. exact (MK_COMB (@lem3582021 _91854 _91858 _91859 P f g) (@lem3582029 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582031 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term282 _91854 _91858 _91859 P f g) = (term297 _91854 _91858 _91859 P f g).
Proof. exact (EQ_MP (@lem3582030 _91854 _91858 _91859 P f g) (@lem3582011 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582033 {A : Type'} (P : Prop) (Q : A -> Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3582034 {_91858 _91859 : Type'} (P : Prop) (Q : type805 _91858 _91859) : (term298 _91858 _91859 P Q) = (term299 _91858 _91859 P Q).
Proof. exact (@lem3582033 (_91859 -> _91858) P Q). Qed.
Lemma lem3582035 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term300 _91854 _91858 _91859 x P f g) = (term301 _91854 _91858 _91859 x P f g).
Proof. exact (@lem3582034 _91858 _91859 (term76 _91854 _91858 _91859 P g f x) (term280 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582036 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term302 _91854 _91858 _91859 P f g h) = (term278 _91854 _91858 _91859 P f g h).
Proof. exact (eq_refl (term302 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3582037 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term303 _91854 _91858 _91859 P f g) = (term280 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun h : _91859 -> _91858 => @lem3582036 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3582038 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3582039 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term304 _91854 _91858 _91859 P f g) = (term281 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582038 _91858 _91859) (@lem3582037 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582040 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term292 _91854 _91858 _91859 P g f x) = (term292 _91854 _91858 _91859 P g f x).
Proof. exact (eq_refl (term292 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3582041 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term300 _91854 _91858 _91859 x P f g) = (term294 _91854 _91858 _91859 x P f g).
Proof. exact (MK_COMB (@lem3582040 _91854 _91858 _91859 P g f x) (@lem3582039 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582043 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term305 _91854 _91858 _91859 x P f g) = (term306 _91854 _91858 _91859 x P f g).
Proof. exact (MK_COMB (@lem3582042) (@lem3582041 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582044 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term302 _91854 _91858 _91859 P f g h) = (term278 _91854 _91858 _91859 P f g h).
Proof. exact (eq_refl (term302 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3582045 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term292 _91854 _91858 _91859 P g f x) = (term292 _91854 _91858 _91859 P g f x).
Proof. exact (eq_refl (term292 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3582046 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term307 _91854 _91858 _91859 x P f g h) = (term308 _91854 _91858 _91859 x P f g h).
Proof. exact (MK_COMB (@lem3582045 _91854 _91858 _91859 P g f x) (@lem3582044 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3582047 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term309 _91854 _91858 _91859 x P f g) = (term310 _91854 _91858 _91859 x P f g).
Proof. exact (fun_ext (fun h : _91859 -> _91858 => @lem3582046 _91854 _91858 _91859 x P f g h)). Qed.
Lemma lem3582048 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3582049 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term301 _91854 _91858 _91859 x P f g) = (term311 _91854 _91858 _91859 x P f g).
Proof. exact (MK_COMB (@lem3582048 _91858 _91859) (@lem3582047 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582050 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term300 _91854 _91858 _91859 x P f g) = (term301 _91854 _91858 _91859 x P f g)) = ((term294 _91854 _91858 _91859 x P f g) = (term311 _91854 _91858 _91859 x P f g)).
Proof. exact (MK_COMB (@lem3582043 _91854 _91858 _91859 x P f g) (@lem3582049 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582051 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term294 _91854 _91858 _91859 x P f g) = (term311 _91854 _91858 _91859 x P f g).
Proof. exact (EQ_MP (@lem3582050 _91854 _91858 _91859 x P f g) (@lem3582035 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582052 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term296 _91854 _91858 _91859 P f g) = (term312 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3582051 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582053 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3582054 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term297 _91854 _91858 _91859 P f g) = (term313 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582053 _91859) (@lem3582052 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582055 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term282 _91854 _91858 _91859 P f g) = (term313 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3582031 _91854 _91858 _91859 P f g) (@lem3582054 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582056 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term179 _91854 _91858 _91859 P f g) = (term313 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3582007 _91854 _91858 _91859 P f g) (@lem3582055 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582057 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term180 _91854 _91858 _91859 P f g) = (term314 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3581951 _91854 _91858 _91859 P f g) (@lem3582056 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582061 {A : Type'} (P : A -> Prop) (Q : Prop) : (term315 A P Q) = (term316 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3582062 {_91858 _91859 : Type'} (P : type805 _91858 _91859) (Q : Prop) : (term317 _91858 _91859 P Q) = (term318 _91858 _91859 P Q).
Proof. exact (@lem3582061 (_91859 -> _91858) P Q). Qed.
Lemma lem3582063 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term319 _91854 _91858 _91859 P f g) = (term320 _91854 _91858 _91859 P f g).
Proof. exact (@lem3582062 _91858 _91859 (term252 _91854 _91858 _91859 P f g) (term313 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582064 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term321 _91854 _91858 _91859 P f g y) = (term251 _91854 _91858 _91859 y P f g).
Proof. exact (eq_refl (term321 _91854 _91858 _91859 P f g y)). Qed.
Lemma lem3582065 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term322 _91854 _91858 _91859 P f g) = (term252 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun y : _91859 -> _91858 => @lem3582064 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582066 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3582067 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term323 _91854 _91858 _91859 P f g) = (term253 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582066 _91858 _91859) (@lem3582065 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3582069 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term324 _91854 _91858 _91859 P f g) = (term254 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582068) (@lem3582067 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582070 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term313 _91854 _91858 _91859 P f g) = (term313 _91854 _91858 _91859 P f g).
Proof. exact (eq_refl (term313 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582071 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term319 _91854 _91858 _91859 P f g) = (term314 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582069 _91854 _91858 _91859 P f g) (@lem3582070 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582073 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term325 _91854 _91858 _91859 P f g) = (term326 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582072) (@lem3582071 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582074 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term321 _91854 _91858 _91859 P f g y) = (term251 _91854 _91858 _91859 y P f g).
Proof. exact (eq_refl (term321 _91854 _91858 _91859 P f g y)). Qed.
Lemma lem3582075 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3582076 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term327 _91854 _91858 _91859 P f g y) = (term328 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3582075) (@lem3582074 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582077 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term313 _91854 _91858 _91859 P f g) = (term313 _91854 _91858 _91859 P f g).
Proof. exact (eq_refl (term313 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582078 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term329 _91854 _91858 _91859 y P f g) = (term330 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3582076 _91854 _91858 _91859 y P f g) (@lem3582077 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582079 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term331 _91854 _91858 _91859 P f g) = (term332 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun y : _91859 -> _91858 => @lem3582078 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582080 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3582081 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term320 _91854 _91858 _91859 P f g) = (term333 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582080 _91858 _91859) (@lem3582079 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582082 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term319 _91854 _91858 _91859 P f g) = (term320 _91854 _91858 _91859 P f g)) = ((term314 _91854 _91858 _91859 P f g) = (term333 _91854 _91858 _91859 P f g)).
Proof. exact (MK_COMB (@lem3582073 _91854 _91858 _91859 P f g) (@lem3582081 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582083 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term314 _91854 _91858 _91859 P f g) = (term333 _91854 _91858 _91859 P f g).
Proof. exact (EQ_MP (@lem3582082 _91854 _91858 _91859 P f g) (@lem3582063 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582085 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term153 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3582086 {_91859 : Type'} (P : _91859 -> Prop) (Q : _91859 -> Prop) : (term153 _91859 P Q) = (term152 _91859 P Q).
Proof. exact (@lem3582085 _91859 P Q). Qed.
Lemma lem3582087 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term334 _91854 _91858 _91859 y P f g) = (term335 _91854 _91858 _91859 y P f g).
Proof. exact (@lem3582086 _91859 (term250 _91854 _91858 _91859 y P f g) (term312 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582088 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term336 _91854 _91858 _91859 y P f g x) = (term248 _91854 _91858 _91859 y P f x g).
Proof. exact (eq_refl (term336 _91854 _91858 _91859 y P f g x)). Qed.
Lemma lem3582089 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term337 _91854 _91858 _91859 y P f g) = (term250 _91854 _91858 _91859 y P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3582088 _91854 _91858 _91859 y P f x g)). Qed.
Lemma lem3582090 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3582091 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term338 _91854 _91858 _91859 y P f g) = (term251 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3582090 _91859) (@lem3582089 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3582093 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term339 _91854 _91858 _91859 y P f g) = (term328 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3582092) (@lem3582091 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582094 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term340 _91854 _91858 _91859 P f g x) = (term311 _91854 _91858 _91859 x P f g).
Proof. exact (eq_refl (term340 _91854 _91858 _91859 P f g x)). Qed.
Lemma lem3582095 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term341 _91854 _91858 _91859 P f g) = (term312 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3582094 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582096 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3582097 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term342 _91854 _91858 _91859 P f g) = (term313 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582096 _91859) (@lem3582095 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582098 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term334 _91854 _91858 _91859 y P f g) = (term330 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3582093 _91854 _91858 _91859 y P f g) (@lem3582097 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582100 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term343 _91854 _91858 _91859 y P f g) = (term344 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3582099) (@lem3582098 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582101 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term336 _91854 _91858 _91859 y P f g x) = (term248 _91854 _91858 _91859 y P f x g).
Proof. exact (eq_refl (term336 _91854 _91858 _91859 y P f g x)). Qed.
Lemma lem3582102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3582103 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term345 _91854 _91858 _91859 y P f g x) = (term346 _91854 _91858 _91859 y P f x g).
Proof. exact (MK_COMB (@lem3582102) (@lem3582101 _91854 _91858 _91859 y P f x g)). Qed.
Lemma lem3582104 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term340 _91854 _91858 _91859 P f g x) = (term311 _91854 _91858 _91859 x P f g).
Proof. exact (eq_refl (term340 _91854 _91858 _91859 P f g x)). Qed.
Lemma lem3582105 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term347 _91854 _91858 _91859 y P f g x) = (term348 _91854 _91858 _91859 y x P f g).
Proof. exact (MK_COMB (@lem3582103 _91854 _91858 _91859 y P f x g) (@lem3582104 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582106 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term349 _91854 _91858 _91859 y P f g) = (term350 _91854 _91858 _91859 y P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3582105 _91854 _91858 _91859 y x P f g)). Qed.
Lemma lem3582107 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3582108 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term335 _91854 _91858 _91859 y P f g) = (term351 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3582107 _91859) (@lem3582106 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582109 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term334 _91854 _91858 _91859 y P f g) = (term335 _91854 _91858 _91859 y P f g)) = ((term330 _91854 _91858 _91859 y P f g) = (term351 _91854 _91858 _91859 y P f g)).
Proof. exact (MK_COMB (@lem3582100 _91854 _91858 _91859 y P f g) (@lem3582108 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582110 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term330 _91854 _91858 _91859 y P f g) = (term351 _91854 _91858 _91859 y P f g).
Proof. exact (EQ_MP (@lem3582109 _91854 _91858 _91859 y P f g) (@lem3582087 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582112 {A : Type'} (P : Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3582113 {_91858 _91859 : Type'} (P : Prop) (Q : type805 _91858 _91859) : (term352 _91858 _91859 P Q) = (term353 _91858 _91859 P Q).
Proof. exact (@lem3582112 (_91859 -> _91858) P Q). Qed.
Lemma lem3582114 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term354 _91854 _91858 _91859 y x P f g) = (term355 _91854 _91858 _91859 y x P f g).
Proof. exact (@lem3582113 _91858 _91859 (term248 _91854 _91858 _91859 y P f x g) (term310 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582115 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term356 _91854 _91858 _91859 x P f g h) = (term308 _91854 _91858 _91859 x P f g h).
Proof. exact (eq_refl (term356 _91854 _91858 _91859 x P f g h)). Qed.
Lemma lem3582116 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term357 _91854 _91858 _91859 x P f g) = (term310 _91854 _91858 _91859 x P f g).
Proof. exact (fun_ext (fun h : _91859 -> _91858 => @lem3582115 _91854 _91858 _91859 x P f g h)). Qed.
Lemma lem3582117 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3582118 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term358 _91854 _91858 _91859 x P f g) = (term311 _91854 _91858 _91859 x P f g).
Proof. exact (MK_COMB (@lem3582117 _91858 _91859) (@lem3582116 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582119 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term346 _91854 _91858 _91859 y P f x g) = (term346 _91854 _91858 _91859 y P f x g).
Proof. exact (eq_refl (term346 _91854 _91858 _91859 y P f x g)). Qed.
Lemma lem3582120 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term354 _91854 _91858 _91859 y x P f g) = (term348 _91854 _91858 _91859 y x P f g).
Proof. exact (MK_COMB (@lem3582119 _91854 _91858 _91859 y P f x g) (@lem3582118 _91854 _91858 _91859 x P f g)). Qed.
Lemma lem3582121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582122 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term359 _91854 _91858 _91859 y x P f g) = (term360 _91854 _91858 _91859 y x P f g).
Proof. exact (MK_COMB (@lem3582121) (@lem3582120 _91854 _91858 _91859 y x P f g)). Qed.
Lemma lem3582123 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term356 _91854 _91858 _91859 x P f g h) = (term308 _91854 _91858 _91859 x P f g h).
Proof. exact (eq_refl (term356 _91854 _91858 _91859 x P f g h)). Qed.
Lemma lem3582124 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term346 _91854 _91858 _91859 y P f x g) = (term346 _91854 _91858 _91859 y P f x g).
Proof. exact (eq_refl (term346 _91854 _91858 _91859 y P f x g)). Qed.
Lemma lem3582125 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term361 _91854 _91858 _91859 y x P f g h) = (term362 _91854 _91858 _91859 y x P f g h).
Proof. exact (MK_COMB (@lem3582124 _91854 _91858 _91859 y P f x g) (@lem3582123 _91854 _91858 _91859 x P f g h)). Qed.
Lemma lem3582126 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term363 _91854 _91858 _91859 y x P f g) = (term364 _91854 _91858 _91859 y x P f g).
Proof. exact (fun_ext (fun h : _91859 -> _91858 => @lem3582125 _91854 _91858 _91859 y x P f g h)). Qed.
Lemma lem3582127 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3582128 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term355 _91854 _91858 _91859 y x P f g) = (term365 _91854 _91858 _91859 y x P f g).
Proof. exact (MK_COMB (@lem3582127 _91858 _91859) (@lem3582126 _91854 _91858 _91859 y x P f g)). Qed.
Lemma lem3582129 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : ((term354 _91854 _91858 _91859 y x P f g) = (term355 _91854 _91858 _91859 y x P f g)) = ((term348 _91854 _91858 _91859 y x P f g) = (term365 _91854 _91858 _91859 y x P f g)).
Proof. exact (MK_COMB (@lem3582122 _91854 _91858 _91859 y x P f g) (@lem3582128 _91854 _91858 _91859 y x P f g)). Qed.
Lemma lem3582130 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term348 _91854 _91858 _91859 y x P f g) = (term365 _91854 _91858 _91859 y x P f g).
Proof. exact (EQ_MP (@lem3582129 _91854 _91858 _91859 y x P f g) (@lem3582114 _91854 _91858 _91859 y x P f g)). Qed.
Lemma lem3582131 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term350 _91854 _91858 _91859 y P f g) = (term366 _91854 _91858 _91859 y P f g).
Proof. exact (fun_ext (fun x : _91859 => @lem3582130 _91854 _91858 _91859 y x P f g)). Qed.
Lemma lem3582132 {_91859 : Type'} : (@ex _91859) = (@ex _91859).
Proof. exact (eq_refl (@ex _91859)). Qed.
Lemma lem3582133 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term351 _91854 _91858 _91859 y P f g) = (term367 _91854 _91858 _91859 y P f g).
Proof. exact (MK_COMB (@lem3582132 _91859) (@lem3582131 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582134 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term330 _91854 _91858 _91859 y P f g) = (term367 _91854 _91858 _91859 y P f g).
Proof. exact (TRANS (@lem3582110 _91854 _91858 _91859 y P f g) (@lem3582133 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582135 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term332 _91854 _91858 _91859 P f g) = (term368 _91854 _91858 _91859 P f g).
Proof. exact (fun_ext (fun y : _91859 -> _91858 => @lem3582134 _91854 _91858 _91859 y P f g)). Qed.
Lemma lem3582136 {_91858 _91859 : Type'} : (@ex (_91859 -> _91858)) = (@ex (_91859 -> _91858)).
Proof. exact (eq_refl (@ex (_91859 -> _91858))). Qed.
Lemma lem3582137 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term333 _91854 _91858 _91859 P f g) = (term369 _91854 _91858 _91859 P f g).
Proof. exact (MK_COMB (@lem3582136 _91858 _91859) (@lem3582135 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582138 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term314 _91854 _91858 _91859 P f g) = (term369 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3582083 _91854 _91858 _91859 P f g) (@lem3582137 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582139 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term180 _91854 _91858 _91859 P f g) = (term369 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3582057 _91854 _91858 _91859 P f g) (@lem3582138 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582140 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term122 _91854 _91858 _91859 P f g) = (term369 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3581842 _91854 _91858 _91859 P f g) (@lem3582139 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582141 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term63 _91854 _91858 _91859 P f g) = (term369 _91854 _91858 _91859 P f g).
Proof. exact (TRANS (@lem3581581 _91854 _91858 _91859 P f g) (@lem3582140 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582142 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h1 : term63 _91854 _91858 _91859 P f g) : term369 _91854 _91858 _91859 P f g.
Proof. exact (EQ_MP (@lem3582141 _91854 _91858 _91859 P f g) (@lem3581490 _91854 _91858 _91859 P f g h1)). Qed.
Lemma lem3582143 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h1 : term367 _91854 _91858 _91859 y P f g) : term367 _91854 _91858 _91859 y P f g.
Proof. exact (h1). Qed.
Lemma lem3582144 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h1 : term365 _91854 _91858 _91859 y x P f g) : term365 _91854 _91858 _91859 y x P f g.
Proof. exact (h1). Qed.
Lemma lem3582145 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term362 _91854 _91858 _91859 y x P f g h) : term362 _91854 _91858 _91859 y x P f g h.
Proof. exact (h1). Qed.
Lemma lem3582164 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (x : _91859) : (term274 _91854 _91858 _91859 P f g h x) = (term274 _91854 _91858 _91859 P f g h x).
Proof. exact (eq_refl (term274 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3582165 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term276 _91854 _91858 _91859 P f g h) = (term276 _91854 _91858 _91859 P f g h).
Proof. exact (fun_ext (fun x : _91859 => @lem3582164 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3582166 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3582167 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term278 _91854 _91858 _91859 P f g h) = (term278 _91854 _91858 _91859 P f g h).
Proof. exact (MK_COMB (@lem3582166 _91859) (@lem3582165 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3582178 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : (term70 _91854 _91858 _91859 g y f x) = (term70 _91854 _91858 _91859 g y f x).
Proof. exact (eq_refl (term70 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3582179 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term72 _91854 _91858 _91859 g f x) = (term72 _91854 _91858 _91859 g f x).
Proof. exact (fun_ext (fun y : _91858 => @lem3582178 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3582180 {_91858 : Type'} : (@all _91858) = (@all _91858).
Proof. exact (eq_refl (@all _91858)). Qed.
Lemma lem3582181 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term73 _91854 _91858 _91859 g f x) = (term73 _91854 _91858 _91859 g f x).
Proof. exact (MK_COMB (@lem3582180 _91858) (@lem3582179 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3582186 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term74 _91859 P x) = (term74 _91859 P x).
Proof. exact (eq_refl (term74 _91859 P x)). Qed.
Lemma lem3582187 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term76 _91854 _91858 _91859 P g f x) = (term76 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3582186 _91859 P x) (@lem3582181 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3582188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3582189 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term292 _91854 _91858 _91859 P g f x) = (term292 _91854 _91858 _91859 P g f x).
Proof. exact (MK_COMB (@lem3582188) (@lem3582187 _91854 _91858 _91859 P g f x)). Qed.
Lemma lem3582190 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term308 _91854 _91858 _91859 x P f g h) = (term308 _91854 _91858 _91859 x P f g h).
Proof. exact (MK_COMB (@lem3582189 _91854 _91858 _91859 P g f x) (@lem3582167 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3582201 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term132 _91854 _91858 _91859 f x g h) = (term132 _91854 _91858 _91859 f x g h).
Proof. exact (eq_refl (term132 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3582202 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term128 _91854 _91858 _91859 f x g) = (term128 _91854 _91858 _91859 f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3582201 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3582203 {_91858 : Type'} : (@all _91858) = (@all _91858).
Proof. exact (eq_refl (@all _91858)). Qed.
Lemma lem3582204 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term144 _91854 _91858 _91859 f x g) = (term144 _91854 _91858 _91859 f x g).
Proof. exact (MK_COMB (@lem3582203 _91858) (@lem3582202 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3582209 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term74 _91859 P x) = (term74 _91859 P x).
Proof. exact (eq_refl (term74 _91859 P x)). Qed.
Lemma lem3582210 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term147 _91854 _91858 _91859 P f x g) = (term147 _91854 _91858 _91859 P f x g).
Proof. exact (MK_COMB (@lem3582209 _91859 P x) (@lem3582204 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3582229 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (x : _91859) : (term209 _91854 _91858 _91859 P g y f x) = (term209 _91854 _91858 _91859 P g y f x).
Proof. exact (eq_refl (term209 _91854 _91858 _91859 P g y f x)). Qed.
Lemma lem3582230 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term211 _91854 _91858 _91859 P g y f) = (term211 _91854 _91858 _91859 P g y f).
Proof. exact (fun_ext (fun x : _91859 => @lem3582229 _91854 _91858 _91859 P g y f x)). Qed.
Lemma lem3582231 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3582232 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term213 _91854 _91858 _91859 P g y f) = (term213 _91854 _91858 _91859 P g y f).
Proof. exact (MK_COMB (@lem3582231 _91859) (@lem3582230 _91854 _91858 _91859 P g y f)). Qed.
Lemma lem3582233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3582234 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term232 _91854 _91858 _91859 P g y f) = (term232 _91854 _91858 _91859 P g y f).
Proof. exact (MK_COMB (@lem3582233) (@lem3582232 _91854 _91858 _91859 P g y f)). Qed.
Lemma lem3582235 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term248 _91854 _91858 _91859 y P f x g) = (term248 _91854 _91858 _91859 y P f x g).
Proof. exact (MK_COMB (@lem3582234 _91854 _91858 _91859 P g y f) (@lem3582210 _91854 _91858 _91859 P f x g)). Qed.
Lemma lem3582236 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3582237 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term346 _91854 _91858 _91859 y P f x g) = (term346 _91854 _91858 _91859 y P f x g).
Proof. exact (MK_COMB (@lem3582236) (@lem3582235 _91854 _91858 _91859 y P f x g)). Qed.
Lemma lem3582238 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term362 _91854 _91858 _91859 y x P f g h) = (term362 _91854 _91858 _91859 y x P f g h).
Proof. exact (MK_COMB (@lem3582237 _91854 _91858 _91859 y P f x g) (@lem3582190 _91854 _91858 _91859 x P f g h)). Qed.
Lemma lem3582239 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term362 _91854 _91858 _91859 y x P f g h) : term362 _91854 _91858 _91859 y x P f g h.
Proof. exact (EQ_MP (@lem3582238 _91854 _91858 _91859 y x P f g h) (@lem3582145 _91854 _91858 _91859 y x P f g h h1)). Qed.
Lemma lem3582240 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term248 _91854 _91858 _91859 y P f x g.
Proof. exact (h1). Qed.
Lemma lem3582241 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term308 _91854 _91858 _91859 x P f g h.
Proof. exact (h1). Qed.
Lemma lem3582242 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term147 _91854 _91858 _91859 P f x g.
Proof. exact (proj2 (@lem3582240 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582243 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term213 _91854 _91858 _91859 P g y f.
Proof. exact (proj1 (@lem3582240 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582244 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term144 _91854 _91858 _91859 f x g.
Proof. exact (proj2 (@lem3582242 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582246 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term278 _91854 _91858 _91859 P f g h.
Proof. exact (proj2 (@lem3582241 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582247 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term76 _91854 _91858 _91859 P g f x.
Proof. exact (proj1 (@lem3582241 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582248 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term73 _91854 _91858 _91859 g f x.
Proof. exact (proj2 (@lem3582247 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582257 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (x : _91859) : (term209 _91854 _91858 _91859 P g y f x) = (term209 _91854 _91858 _91859 P g y f x).
Proof. exact (eq_refl (term209 _91854 _91858 _91859 P g y f x)). Qed.
Lemma lem3582258 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term211 _91854 _91858 _91859 P g y f) = (term211 _91854 _91858 _91859 P g y f).
Proof. exact (fun_ext (fun x : _91859 => @lem3582257 _91854 _91858 _91859 P g y f x)). Qed.
Lemma lem3582259 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3582261 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) : (term213 _91854 _91858 _91859 P g y f) = (term213 _91854 _91858 _91859 P g y f).
Proof. exact (MK_COMB (@lem3582259 _91859) (@lem3582258 _91854 _91858 _91859 P g y f)). Qed.
Lemma lem3582262 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term213 _91854 _91858 _91859 P g y f.
Proof. exact (EQ_MP (@lem3582261 _91854 _91858 _91859 P g y f) (@lem3582243 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582268 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h : _91858) : (term132 _91854 _91858 _91859 f x g h) = (term132 _91854 _91858 _91859 f x g h).
Proof. exact (eq_refl (term132 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3582269 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term128 _91854 _91858 _91859 f x g) = (term128 _91854 _91858 _91859 f x g).
Proof. exact (fun_ext (fun h : _91858 => @lem3582268 _91854 _91858 _91859 f x g h)). Qed.
Lemma lem3582270 {_91858 : Type'} : (@all _91858) = (@all _91858).
Proof. exact (eq_refl (@all _91858)). Qed.
Lemma lem3582272 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) : (term144 _91854 _91858 _91859 f x g) = (term144 _91854 _91858 _91859 f x g).
Proof. exact (MK_COMB (@lem3582270 _91858) (@lem3582269 _91854 _91858 _91859 f x g)). Qed.
Lemma lem3582273 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term144 _91854 _91858 _91859 f x g.
Proof. exact (EQ_MP (@lem3582272 _91854 _91858 _91859 f x g) (@lem3582244 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582281 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (x : _91859) : (term274 _91854 _91858 _91859 P f g h x) = (term274 _91854 _91858 _91859 P f g h x).
Proof. exact (eq_refl (term274 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3582282 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term276 _91854 _91858 _91859 P f g h) = (term276 _91854 _91858 _91859 P f g h).
Proof. exact (fun_ext (fun x : _91859 => @lem3582281 _91854 _91858 _91859 P f g h x)). Qed.
Lemma lem3582283 {_91859 : Type'} : (@all _91859) = (@all _91859).
Proof. exact (eq_refl (@all _91859)). Qed.
Lemma lem3582285 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) : (term278 _91854 _91858 _91859 P f g h) = (term278 _91854 _91858 _91859 P f g h).
Proof. exact (MK_COMB (@lem3582283 _91859) (@lem3582282 _91854 _91858 _91859 P f g h)). Qed.
Lemma lem3582286 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term278 _91854 _91858 _91859 P f g h.
Proof. exact (EQ_MP (@lem3582285 _91854 _91858 _91859 P f g h) (@lem3582246 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582292 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91858) (f : _91859 -> _91854) (x : _91859) : (term70 _91854 _91858 _91859 g y f x) = (term70 _91854 _91858 _91859 g y f x).
Proof. exact (eq_refl (term70 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3582293 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term72 _91854 _91858 _91859 g f x) = (term72 _91854 _91858 _91859 g f x).
Proof. exact (fun_ext (fun y : _91858 => @lem3582292 _91854 _91858 _91859 g y f x)). Qed.
Lemma lem3582294 {_91858 : Type'} : (@all _91858) = (@all _91858).
Proof. exact (eq_refl (@all _91858)). Qed.
Lemma lem3582296 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (f : _91859 -> _91854) (x : _91859) : (term73 _91854 _91858 _91859 g f x) = (term73 _91854 _91858 _91859 g f x).
Proof. exact (MK_COMB (@lem3582294 _91858) (@lem3582293 _91854 _91858 _91859 g f x)). Qed.
Lemma lem3582297 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term73 _91854 _91858 _91859 g f x.
Proof. exact (EQ_MP (@lem3582296 _91854 _91858 _91859 g f x) (@lem3582248 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582298 {_91854 _91858 _91859 : Type'} (_38661 : _91859) (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term370 _91854 _91858 _91859 P g y f _38661.
Proof. exact (@lem3582262 _91854 _91858 _91859 y P f x g h1 _38661). Qed.
Lemma lem3582299 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (_38661 : _91859) : (term370 _91854 _91858 _91859 P g y f _38661) = (term209 _91854 _91858 _91859 P g y f _38661).
Proof. exact (eq_refl (term370 _91854 _91858 _91859 P g y f _38661)). Qed.
Lemma lem3582301 {_91854 _91858 _91859 : Type'} (_38662 : _91858) (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term131 _91854 _91858 _91859 f x g _38662.
Proof. exact (@lem3582273 _91854 _91858 _91859 y P f x g h1 _38662). Qed.
Lemma lem3582302 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (_38662 : _91858) : (term131 _91854 _91858 _91859 f x g _38662) = (term132 _91854 _91858 _91859 f x g _38662).
Proof. exact (eq_refl (term131 _91854 _91858 _91859 f x g _38662)). Qed.
Lemma lem3582304 {_91854 _91858 _91859 : Type'} (_38663 : _91859) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term371 _91854 _91858 _91859 P f g h _38663.
Proof. exact (@lem3582286 _91854 _91858 _91859 x P f g h h1 _38663). Qed.
Lemma lem3582305 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (_38663 : _91859) : (term371 _91854 _91858 _91859 P f g h _38663) = (term274 _91854 _91858 _91859 P f g h _38663).
Proof. exact (eq_refl (term371 _91854 _91858 _91859 P f g h _38663)). Qed.
Lemma lem3582307 {_91854 _91858 _91859 : Type'} (_38664 : _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term372 _91854 _91858 _91859 g f x _38664.
Proof. exact (@lem3582297 _91854 _91858 _91859 x P f g h h1 _38664). Qed.
Lemma lem3582308 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (_38664 : _91858) (f : _91859 -> _91854) (x : _91859) : (term372 _91854 _91858 _91859 g f x _38664) = (term70 _91854 _91858 _91859 g _38664 f x).
Proof. exact (eq_refl (term372 _91854 _91858 _91859 g f x _38664)). Qed.
Lemma lem3582315 {_91854 _91858 _91859 : Type'} (_38661 : _91859) (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term209 _91854 _91858 _91859 P g y f _38661.
Proof. exact (EQ_MP (@lem3582299 _91854 _91858 _91859 P g y f _38661) (@lem3582298 _91854 _91858 _91859 _38661 y P f x g h1)). Qed.
Lemma lem3582319 {_91854 _91858 _91859 : Type'} (_38662 : _91858) (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term132 _91854 _91858 _91859 f x g _38662.
Proof. exact (EQ_MP (@lem3582302 _91854 _91858 _91859 f x g _38662) (@lem3582301 _91854 _91858 _91859 _38662 y P f x g h1)). Qed.
Lemma lem3582325 {_91854 _91858 _91859 : Type'} (_38663 : _91859) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term274 _91854 _91858 _91859 P f g h _38663.
Proof. exact (EQ_MP (@lem3582305 _91854 _91858 _91859 P f g h _38663) (@lem3582304 _91854 _91858 _91859 _38663 x P f g h h1)). Qed.
Lemma lem3582329 {_91854 _91858 _91859 : Type'} (_38664 : _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term70 _91854 _91858 _91859 g _38664 f x.
Proof. exact (EQ_MP (@lem3582308 _91854 _91858 _91859 g _38664 f x) (@lem3582307 _91854 _91858 _91859 _38664 x P f g h h1)). Qed.
Lemma lem3582367 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : term373 _91854 x y z.
Proof. exact (@lem21385 _91854 x y z). Qed.
Lemma lem3582373 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : P x.
Proof. exact (proj1 (@lem3582242 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582374 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term374 _91859 P x.
Proof. exact (fun h0 : term159 _91859 P x => @lem3582373 _91854 _91858 _91859 y P f x g h1). Qed.
Lemma lem3582376 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582377 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term374 _91859 P x) = (P x).
Proof. exact (@lem3582376 (P x)). Qed.
Lemma lem3582378 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : P x.
Proof. exact (EQ_MP (@lem3582377 _91859 P x) (@lem3582374 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582384 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3582385 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (P : _91859 -> Prop) (_38661 : _91859) : (term209 _91854 _91858 _91859 P g y f _38661) = (term376 _91854 _91858 _91859 g y f P _38661).
Proof. exact (@lem3582384 ((term377 _91854 _91858 _91859 g y _38661) = (f _38661)) (term159 _91859 P _38661)). Qed.
Lemma lem3582393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582394 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (P : _91859 -> Prop) (_38661 : _91859) : (term378 _91854 _91858 _91859 P g y f _38661) = (term379 _91854 _91858 _91859 g y f P _38661).
Proof. exact (MK_COMB (@lem3582393) (@lem3582385 _91854 _91858 _91859 g y f P _38661)). Qed.
Lemma lem3582402 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (P : _91859 -> Prop) (_38661 : _91859) : (term376 _91854 _91858 _91859 g y f P _38661) = (term376 _91854 _91858 _91859 g y f P _38661).
Proof. exact (eq_refl (term376 _91854 _91858 _91859 g y f P _38661)). Qed.
Lemma lem3582403 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (P : _91859 -> Prop) (_38661 : _91859) : ((term209 _91854 _91858 _91859 P g y f _38661) = (term376 _91854 _91858 _91859 g y f P _38661)) = ((term376 _91854 _91858 _91859 g y f P _38661) = (term376 _91854 _91858 _91859 g y f P _38661)).
Proof. exact (MK_COMB (@lem3582394 _91854 _91858 _91859 g y f P _38661) (@lem3582402 _91854 _91858 _91859 g y f P _38661)). Qed.
Lemma lem3582405 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3582406 (x : Prop) : (x = x) = True.
Proof. exact (@lem3582405 Prop x). Qed.
Lemma lem3582407 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (P : _91859 -> Prop) (_38661 : _91859) : ((term376 _91854 _91858 _91859 g y f P _38661) = (term376 _91854 _91858 _91859 g y f P _38661)) = True.
Proof. exact (@lem3582406 (term376 _91854 _91858 _91859 g y f P _38661)). Qed.
Lemma lem3582408 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (P : _91859 -> Prop) (_38661 : _91859) : ((term209 _91854 _91858 _91859 P g y f _38661) = (term376 _91854 _91858 _91859 g y f P _38661)) = True.
Proof. exact (TRANS (@lem3582403 _91854 _91858 _91859 g y f P _38661) (@lem3582407 _91854 _91858 _91859 g y f P _38661)). Qed.
Lemma lem3582409 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (P : _91859 -> Prop) (_38661 : _91859) : True = ((term209 _91854 _91858 _91859 P g y f _38661) = (term376 _91854 _91858 _91859 g y f P _38661)).
Proof. exact (SYM (@lem3582408 _91854 _91858 _91859 g y f P _38661)). Qed.
Lemma lem3582410 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (P : _91859 -> Prop) (_38661 : _91859) : (term209 _91854 _91858 _91859 P g y f _38661) = (term376 _91854 _91858 _91859 g y f P _38661).
Proof. exact (EQ_MP (@lem3582409 _91854 _91858 _91859 g y f P _38661) (@lem0)). Qed.
Lemma lem3582411 {_91854 _91858 _91859 : Type'} (_38661 : _91859) (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term376 _91854 _91858 _91859 g y f P _38661.
Proof. exact (EQ_MP (@lem3582410 _91854 _91858 _91859 g y f P _38661) (@lem3582315 _91854 _91858 _91859 _38661 y P f x g h1)). Qed.
Lemma lem3582413 (b : Prop) (a : Prop) : (a \/ b) = (term380 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3582414 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (_38661 : _91859) : (term376 _91854 _91858 _91859 g y f P _38661) = (term381 _91854 _91858 _91859 P g y f _38661).
Proof. exact (@lem3582413 (term159 _91859 P _38661) ((term377 _91854 _91858 _91859 g y _38661) = (f _38661))). Qed.
Lemma lem3582416 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3582417 {_91859 : Type'} (P : _91859 -> Prop) (_38661 : _91859) : (term382 _91859 P _38661) = (P _38661).
Proof. exact (@lem3582416 (P _38661)). Qed.
Lemma lem3582418 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3582419 {_91859 : Type'} (P : _91859 -> Prop) (_38661 : _91859) : (term383 _91859 P _38661) = (term59 _91859 P _38661).
Proof. exact (MK_COMB (@lem3582418) (@lem3582417 _91859 P _38661)). Qed.
Lemma lem3582420 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (_38661 : _91859) : ((term377 _91854 _91858 _91859 g y _38661) = (f _38661)) = ((term377 _91854 _91858 _91859 g y _38661) = (f _38661)).
Proof. exact (eq_refl ((term377 _91854 _91858 _91859 g y _38661) = (f _38661))). Qed.
Lemma lem3582421 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (_38661 : _91859) : (term381 _91854 _91858 _91859 P g y f _38661) = (term384 _91854 _91858 _91859 P g y f _38661).
Proof. exact (MK_COMB (@lem3582419 _91859 P _38661) (@lem3582420 _91854 _91858 _91859 g y f _38661)). Qed.
Lemma lem3582422 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (_38661 : _91859) : (term376 _91854 _91858 _91859 g y f P _38661) = (term384 _91854 _91858 _91859 P g y f _38661).
Proof. exact (TRANS (@lem3582414 _91854 _91858 _91859 P g y f _38661) (@lem3582421 _91854 _91858 _91859 P g y f _38661)). Qed.
Lemma lem3582425 {_91854 _91858 _91859 : Type'} (_38661 : _91859) (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term384 _91854 _91858 _91859 P g y f _38661.
Proof. exact (EQ_MP (@lem3582422 _91854 _91858 _91859 P g y f _38661) (@lem3582411 _91854 _91858 _91859 _38661 y P f x g h1)). Qed.
Lemma lem3582426 {_91854 _91858 _91859 : Type'} (_38661 : _91859) (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term384 _91854 _91858 _91859 P g y f _38661.
Proof. exact (@lem3582425 _91854 _91858 _91859 _38661 y P f x g h1). Qed.
Lemma lem3582427 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term384 _91854 _91858 _91859 P g y f x.
Proof. exact (@lem3582426 _91854 _91858 _91859 x y P f x g h1). Qed.
Lemma lem3582430 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : (term377 _91854 _91858 _91859 g y x) = (f x).
Proof. exact (@lem3582427 _91854 _91858 _91859 y P f x g h1 (@lem3582378 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582431 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term385 _91854 _91858 _91859 g y f x.
Proof. exact (fun h0 : term386 _91854 _91858 _91859 g y f x => @lem3582430 _91854 _91858 _91859 y P f x g h1). Qed.
Lemma lem3582433 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582434 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (f : _91859 -> _91854) (x : _91859) : (term385 _91854 _91858 _91859 g y f x) = ((term377 _91854 _91858 _91859 g y x) = (f x)).
Proof. exact (@lem3582433 ((term377 _91854 _91858 _91859 g y x) = (f x))). Qed.
Lemma lem3582435 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : (term377 _91854 _91858 _91859 g y x) = (f x).
Proof. exact (EQ_MP (@lem3582434 _91854 _91858 _91859 g y f x) (@lem3582431 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582437 {_91854 : Type'} (x : _91854) : x = x.
Proof. exact (@lem21386 _91854 x). Qed.
Lemma lem3582438 {_91854 : Type'} (x : _91854) : x = x.
Proof. exact (@lem3582437 _91854 x). Qed.
Lemma lem3582439 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (x : _91859) : (term377 _91854 _91858 _91859 g y x) = (term377 _91854 _91858 _91859 g y x).
Proof. exact (@lem3582438 _91854 (term377 _91854 _91858 _91859 g y x)). Qed.
Lemma lem3582440 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (x : _91859) : term387 _91854 _91858 _91859 g y x.
Proof. exact (fun h0 : term388 _91854 _91858 _91859 g y x => @lem3582439 _91854 _91858 _91859 g y x). Qed.
Lemma lem3582442 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582443 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (x : _91859) : (term387 _91854 _91858 _91859 g y x) = ((term377 _91854 _91858 _91859 g y x) = (term377 _91854 _91858 _91859 g y x)).
Proof. exact (@lem3582442 ((term377 _91854 _91858 _91859 g y x) = (term377 _91854 _91858 _91859 g y x))). Qed.
Lemma lem3582444 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (y : _91859 -> _91858) (x : _91859) : (term377 _91854 _91858 _91859 g y x) = (term377 _91854 _91858 _91859 g y x).
Proof. exact (EQ_MP (@lem3582443 _91854 _91858 _91859 g y x) (@lem3582440 _91854 _91858 _91859 g y x)). Qed.
Lemma lem3582462 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3582463 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term389 _91854 x y z) = (term390 _91854 y x z).
Proof. exact (@lem3582462 (y = z) (term391 _91854 x z)). Qed.
Lemma lem3582473 {_91854 : Type'} (x : _91854) (y : _91854) : (term392 _91854 x y) = (term392 _91854 x y).
Proof. exact (eq_refl (term392 _91854 x y)). Qed.
Lemma lem3582474 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term373 _91854 x y z) = (term393 _91854 y x z).
Proof. exact (MK_COMB (@lem3582473 _91854 x y) (@lem3582463 _91854 y x z)). Qed.
Lemma lem3582478 (q : Prop) (p : Prop) (r : Prop) : (term394 p q r) = (term394 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3582479 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term393 _91854 y x z) = (term395 _91854 y x z).
Proof. exact (@lem3582478 (y = z) (term391 _91854 x y) (term391 _91854 x z)). Qed.
Lemma lem3582501 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term373 _91854 x y z) = (term395 _91854 y x z).
Proof. exact (TRANS (@lem3582474 _91854 y x z) (@lem3582479 _91854 y x z)). Qed.
Lemma lem3582502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582503 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term396 _91854 x y z) = (term397 _91854 y x z).
Proof. exact (MK_COMB (@lem3582502) (@lem3582501 _91854 y x z)). Qed.
Lemma lem3582525 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term395 _91854 y x z) = (term395 _91854 y x z).
Proof. exact (eq_refl (term395 _91854 y x z)). Qed.
Lemma lem3582526 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : ((term373 _91854 x y z) = (term395 _91854 y x z)) = ((term395 _91854 y x z) = (term395 _91854 y x z)).
Proof. exact (MK_COMB (@lem3582503 _91854 y x z) (@lem3582525 _91854 y x z)). Qed.
Lemma lem3582528 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3582529 (x : Prop) : (x = x) = True.
Proof. exact (@lem3582528 Prop x). Qed.
Lemma lem3582530 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : ((term395 _91854 y x z) = (term395 _91854 y x z)) = True.
Proof. exact (@lem3582529 (term395 _91854 y x z)). Qed.
Lemma lem3582531 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : ((term373 _91854 x y z) = (term395 _91854 y x z)) = True.
Proof. exact (TRANS (@lem3582526 _91854 y x z) (@lem3582530 _91854 y x z)). Qed.
Lemma lem3582532 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : True = ((term373 _91854 x y z) = (term395 _91854 y x z)).
Proof. exact (SYM (@lem3582531 _91854 y x z)). Qed.
Lemma lem3582533 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term373 _91854 x y z) = (term395 _91854 y x z).
Proof. exact (EQ_MP (@lem3582532 _91854 y x z) (@lem0)). Qed.
Lemma lem3582534 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : term395 _91854 y x z.
Proof. exact (EQ_MP (@lem3582533 _91854 y x z) (@lem3582367 _91854 x y z)). Qed.
Lemma lem3582536 (b : Prop) (a : Prop) : (a \/ b) = (term380 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3582537 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : (term395 _91854 y x z) = (term398 _91854 x y z).
Proof. exact (@lem3582536 (term399 _91854 y x z) (y = z)). Qed.
Lemma lem3582539 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3582540 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term402 _91854 y x z) = (term403 _91854 y x z).
Proof. exact (@lem3582539 (term391 _91854 x y) (term391 _91854 x z)). Qed.
Lemma lem3582542 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3582543 {_91854 : Type'} (x : _91854) (y : _91854) : (term404 _91854 x y) = (x = y).
Proof. exact (@lem3582542 (x = y)). Qed.
Lemma lem3582544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3582545 {_91854 : Type'} (x : _91854) (y : _91854) : (term405 _91854 x y) = (term406 _91854 x y).
Proof. exact (MK_COMB (@lem3582544) (@lem3582543 _91854 x y)). Qed.
Lemma lem3582547 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3582548 {_91854 : Type'} (x : _91854) (z : _91854) : (term404 _91854 x z) = (x = z).
Proof. exact (@lem3582547 (x = z)). Qed.
Lemma lem3582549 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term403 _91854 y x z) = (term407 _91854 y x z).
Proof. exact (MK_COMB (@lem3582545 _91854 x y) (@lem3582548 _91854 x z)). Qed.
Lemma lem3582550 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term402 _91854 y x z) = (term407 _91854 y x z).
Proof. exact (TRANS (@lem3582540 _91854 y x z) (@lem3582549 _91854 y x z)). Qed.
Lemma lem3582551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3582552 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term408 _91854 y x z) = (term409 _91854 y x z).
Proof. exact (MK_COMB (@lem3582551) (@lem3582550 _91854 y x z)). Qed.
Lemma lem3582553 {_91854 : Type'} (y : _91854) (z : _91854) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3582554 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : (term398 _91854 x y z) = (term410 _91854 x y z).
Proof. exact (MK_COMB (@lem3582552 _91854 y x z) (@lem3582553 _91854 y z)). Qed.
Lemma lem3582555 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : (term395 _91854 y x z) = (term410 _91854 x y z).
Proof. exact (TRANS (@lem3582537 _91854 x y z) (@lem3582554 _91854 x y z)). Qed.
Lemma lem3582557 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term411 _91854 _91858 _91859 f g y x.
Proof. exact (conj (@lem3582435 _91854 _91858 _91859 y P f x g h1) (@lem3582444 _91854 _91858 _91859 g y x)). Qed.
Lemma lem3582559 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : term410 _91854 x y z.
Proof. exact (EQ_MP (@lem3582555 _91854 x y z) (@lem3582534 _91854 y x z)). Qed.
Lemma lem3582560 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : term410 _91854 x y z.
Proof. exact (@lem3582559 _91854 x y z). Qed.
Lemma lem3582561 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (y : _91859 -> _91858) (x : _91859) : term412 _91854 _91858 _91859 f g y x.
Proof. exact (@lem3582560 _91854 (term377 _91854 _91858 _91859 g y x) (f x) (term377 _91854 _91858 _91859 g y x)). Qed.
Lemma lem3582564 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : (f x) = (term377 _91854 _91858 _91859 g y x).
Proof. exact (@lem3582561 _91854 _91858 _91859 f g y x (@lem3582557 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582565 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term413 _91854 _91858 _91859 f g y x.
Proof. exact (fun h0 : term414 _91854 _91858 _91859 f g y x => @lem3582564 _91854 _91858 _91859 y P f x g h1). Qed.
Lemma lem3582567 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582568 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (y : _91859 -> _91858) (x : _91859) : (term413 _91854 _91858 _91859 f g y x) = ((f x) = (term377 _91854 _91858 _91859 g y x)).
Proof. exact (@lem3582567 ((f x) = (term377 _91854 _91858 _91859 g y x))). Qed.
Lemma lem3582569 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : (f x) = (term377 _91854 _91858 _91859 g y x).
Proof. exact (EQ_MP (@lem3582568 _91854 _91858 _91859 f g y x) (@lem3582565 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582572 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3582574 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (_38662 : _91858) : (term132 _91854 _91858 _91859 f x g _38662) = (term415 _91854 _91858 _91859 f x g _38662).
Proof. exact (@lem3582572 ((f x) = (g _38662))). Qed.
Lemma lem3582577 {_91854 _91858 _91859 : Type'} (_38662 : _91858) (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term415 _91854 _91858 _91859 f x g _38662.
Proof. exact (EQ_MP (@lem3582574 _91854 _91858 _91859 f x g _38662) (@lem3582319 _91854 _91858 _91859 _38662 y P f x g h1)). Qed.
Lemma lem3582578 {_91854 _91858 _91859 : Type'} (_38662 : _91858) (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term415 _91854 _91858 _91859 f x g _38662.
Proof. exact (@lem3582577 _91854 _91858 _91859 _38662 y P f x g h1). Qed.
Lemma lem3582579 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term416 _91854 _91858 _91859 f g y x.
Proof. exact (@lem3582578 _91854 _91858 _91859 (y x) y P f x g h1). Qed.
Lemma lem3582582 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : False.
Proof. exact (@lem3582579 _91854 _91858 _91859 y P f x g h1 (@lem3582569 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582583 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : term417.
Proof. exact (fun h0 : ~ False => @lem3582582 _91854 _91858 _91859 y P f x g h1). Qed.
Lemma lem3582585 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582586 : term417 = False.
Proof. exact (@lem3582585 False). Qed.
Lemma lem3582587 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (x : _91859) (g : _91858 -> _91854) (h1 : term248 _91854 _91858 _91859 y P f x g) : False.
Proof. exact (EQ_MP (@lem3582586) (@lem3582583 _91854 _91858 _91859 y P f x g h1)). Qed.
Lemma lem3582625 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : term373 _91854 x y z.
Proof. exact (@lem21385 _91854 x y z). Qed.
Lemma lem3582631 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : P x.
Proof. exact (proj1 (@lem3582247 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582632 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term374 _91859 P x.
Proof. exact (fun h0 : term159 _91859 P x => @lem3582631 _91854 _91858 _91859 x P f g h h1). Qed.
Lemma lem3582634 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582635 {_91859 : Type'} (P : _91859 -> Prop) (x : _91859) : (term374 _91859 P x) = (P x).
Proof. exact (@lem3582634 (P x)). Qed.
Lemma lem3582636 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : P x.
Proof. exact (EQ_MP (@lem3582635 _91859 P x) (@lem3582632 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582642 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3582643 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (P : _91859 -> Prop) (_38663 : _91859) : (term274 _91854 _91858 _91859 P f g h _38663) = (term418 _91854 _91858 _91859 f g h P _38663).
Proof. exact (@lem3582642 ((f _38663) = (term377 _91854 _91858 _91859 g h _38663)) (term159 _91859 P _38663)). Qed.
Lemma lem3582651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582652 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (P : _91859 -> Prop) (_38663 : _91859) : (term419 _91854 _91858 _91859 P f g h _38663) = (term420 _91854 _91858 _91859 f g h P _38663).
Proof. exact (MK_COMB (@lem3582651) (@lem3582643 _91854 _91858 _91859 f g h P _38663)). Qed.
Lemma lem3582660 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (P : _91859 -> Prop) (_38663 : _91859) : (term418 _91854 _91858 _91859 f g h P _38663) = (term418 _91854 _91858 _91859 f g h P _38663).
Proof. exact (eq_refl (term418 _91854 _91858 _91859 f g h P _38663)). Qed.
Lemma lem3582661 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (P : _91859 -> Prop) (_38663 : _91859) : ((term274 _91854 _91858 _91859 P f g h _38663) = (term418 _91854 _91858 _91859 f g h P _38663)) = ((term418 _91854 _91858 _91859 f g h P _38663) = (term418 _91854 _91858 _91859 f g h P _38663)).
Proof. exact (MK_COMB (@lem3582652 _91854 _91858 _91859 f g h P _38663) (@lem3582660 _91854 _91858 _91859 f g h P _38663)). Qed.
Lemma lem3582663 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3582664 (x : Prop) : (x = x) = True.
Proof. exact (@lem3582663 Prop x). Qed.
Lemma lem3582665 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (P : _91859 -> Prop) (_38663 : _91859) : ((term418 _91854 _91858 _91859 f g h P _38663) = (term418 _91854 _91858 _91859 f g h P _38663)) = True.
Proof. exact (@lem3582664 (term418 _91854 _91858 _91859 f g h P _38663)). Qed.
Lemma lem3582666 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (P : _91859 -> Prop) (_38663 : _91859) : ((term274 _91854 _91858 _91859 P f g h _38663) = (term418 _91854 _91858 _91859 f g h P _38663)) = True.
Proof. exact (TRANS (@lem3582661 _91854 _91858 _91859 f g h P _38663) (@lem3582665 _91854 _91858 _91859 f g h P _38663)). Qed.
Lemma lem3582667 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (P : _91859 -> Prop) (_38663 : _91859) : True = ((term274 _91854 _91858 _91859 P f g h _38663) = (term418 _91854 _91858 _91859 f g h P _38663)).
Proof. exact (SYM (@lem3582666 _91854 _91858 _91859 f g h P _38663)). Qed.
Lemma lem3582668 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (P : _91859 -> Prop) (_38663 : _91859) : (term274 _91854 _91858 _91859 P f g h _38663) = (term418 _91854 _91858 _91859 f g h P _38663).
Proof. exact (EQ_MP (@lem3582667 _91854 _91858 _91859 f g h P _38663) (@lem0)). Qed.
Lemma lem3582669 {_91854 _91858 _91859 : Type'} (_38663 : _91859) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term418 _91854 _91858 _91859 f g h P _38663.
Proof. exact (EQ_MP (@lem3582668 _91854 _91858 _91859 f g h P _38663) (@lem3582325 _91854 _91858 _91859 _38663 x P f g h h1)). Qed.
Lemma lem3582671 (b : Prop) (a : Prop) : (a \/ b) = (term380 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3582672 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (_38663 : _91859) : (term418 _91854 _91858 _91859 f g h P _38663) = (term421 _91854 _91858 _91859 P f g h _38663).
Proof. exact (@lem3582671 (term159 _91859 P _38663) ((f _38663) = (term377 _91854 _91858 _91859 g h _38663))). Qed.
Lemma lem3582674 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3582675 {_91859 : Type'} (P : _91859 -> Prop) (_38663 : _91859) : (term382 _91859 P _38663) = (P _38663).
Proof. exact (@lem3582674 (P _38663)). Qed.
Lemma lem3582676 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3582677 {_91859 : Type'} (P : _91859 -> Prop) (_38663 : _91859) : (term383 _91859 P _38663) = (term59 _91859 P _38663).
Proof. exact (MK_COMB (@lem3582676) (@lem3582675 _91859 P _38663)). Qed.
Lemma lem3582678 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (_38663 : _91859) : ((f _38663) = (term377 _91854 _91858 _91859 g h _38663)) = ((f _38663) = (term377 _91854 _91858 _91859 g h _38663)).
Proof. exact (eq_refl ((f _38663) = (term377 _91854 _91858 _91859 g h _38663))). Qed.
Lemma lem3582679 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (_38663 : _91859) : (term421 _91854 _91858 _91859 P f g h _38663) = (term16 _91854 _91858 _91859 P f g h _38663).
Proof. exact (MK_COMB (@lem3582677 _91859 P _38663) (@lem3582678 _91854 _91858 _91859 f g h _38663)). Qed.
Lemma lem3582680 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (_38663 : _91859) : (term418 _91854 _91858 _91859 f g h P _38663) = (term16 _91854 _91858 _91859 P f g h _38663).
Proof. exact (TRANS (@lem3582672 _91854 _91858 _91859 P f g h _38663) (@lem3582679 _91854 _91858 _91859 P f g h _38663)). Qed.
Lemma lem3582683 {_91854 _91858 _91859 : Type'} (_38663 : _91859) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term16 _91854 _91858 _91859 P f g h _38663.
Proof. exact (EQ_MP (@lem3582680 _91854 _91858 _91859 P f g h _38663) (@lem3582669 _91854 _91858 _91859 _38663 x P f g h h1)). Qed.
Lemma lem3582684 {_91854 _91858 _91859 : Type'} (_38663 : _91859) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term16 _91854 _91858 _91859 P f g h _38663.
Proof. exact (@lem3582683 _91854 _91858 _91859 _38663 x P f g h h1). Qed.
Lemma lem3582685 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term16 _91854 _91858 _91859 P f g h x.
Proof. exact (@lem3582684 _91854 _91858 _91859 x x P f g h h1). Qed.
Lemma lem3582688 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : (f x) = (term377 _91854 _91858 _91859 g h x).
Proof. exact (@lem3582685 _91854 _91858 _91859 x P f g h h1 (@lem3582636 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582689 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term413 _91854 _91858 _91859 f g h x.
Proof. exact (fun h0 : term414 _91854 _91858 _91859 f g h x => @lem3582688 _91854 _91858 _91859 x P f g h h1). Qed.
Lemma lem3582691 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582692 {_91854 _91858 _91859 : Type'} (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (x : _91859) : (term413 _91854 _91858 _91859 f g h x) = ((f x) = (term377 _91854 _91858 _91859 g h x)).
Proof. exact (@lem3582691 ((f x) = (term377 _91854 _91858 _91859 g h x))). Qed.
Lemma lem3582693 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : (f x) = (term377 _91854 _91858 _91859 g h x).
Proof. exact (EQ_MP (@lem3582692 _91854 _91858 _91859 f g h x) (@lem3582689 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582695 {_91854 : Type'} (x : _91854) : x = x.
Proof. exact (@lem21386 _91854 x). Qed.
Lemma lem3582696 {_91854 : Type'} (x : _91854) : x = x.
Proof. exact (@lem3582695 _91854 x). Qed.
Lemma lem3582697 {_91854 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) : (f x) = (f x).
Proof. exact (@lem3582696 _91854 (f x)). Qed.
Lemma lem3582698 {_91854 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) : term422 _91854 _91859 f x.
Proof. exact (fun h0 : term423 _91854 _91859 f x => @lem3582697 _91854 _91859 f x). Qed.
Lemma lem3582700 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582701 {_91854 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) : (term422 _91854 _91859 f x) = ((f x) = (f x)).
Proof. exact (@lem3582700 ((f x) = (f x))). Qed.
Lemma lem3582702 {_91854 _91859 : Type'} (f : _91859 -> _91854) (x : _91859) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3582701 _91854 _91859 f x) (@lem3582698 _91854 _91859 f x)). Qed.
Lemma lem3582720 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3582721 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term389 _91854 x y z) = (term390 _91854 y x z).
Proof. exact (@lem3582720 (y = z) (term391 _91854 x z)). Qed.
Lemma lem3582731 {_91854 : Type'} (x : _91854) (y : _91854) : (term392 _91854 x y) = (term392 _91854 x y).
Proof. exact (eq_refl (term392 _91854 x y)). Qed.
Lemma lem3582732 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term373 _91854 x y z) = (term393 _91854 y x z).
Proof. exact (MK_COMB (@lem3582731 _91854 x y) (@lem3582721 _91854 y x z)). Qed.
Lemma lem3582736 (q : Prop) (p : Prop) (r : Prop) : (term394 p q r) = (term394 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3582737 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term393 _91854 y x z) = (term395 _91854 y x z).
Proof. exact (@lem3582736 (y = z) (term391 _91854 x y) (term391 _91854 x z)). Qed.
Lemma lem3582759 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term373 _91854 x y z) = (term395 _91854 y x z).
Proof. exact (TRANS (@lem3582732 _91854 y x z) (@lem3582737 _91854 y x z)). Qed.
Lemma lem3582760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3582761 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term396 _91854 x y z) = (term397 _91854 y x z).
Proof. exact (MK_COMB (@lem3582760) (@lem3582759 _91854 y x z)). Qed.
Lemma lem3582783 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term395 _91854 y x z) = (term395 _91854 y x z).
Proof. exact (eq_refl (term395 _91854 y x z)). Qed.
Lemma lem3582784 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : ((term373 _91854 x y z) = (term395 _91854 y x z)) = ((term395 _91854 y x z) = (term395 _91854 y x z)).
Proof. exact (MK_COMB (@lem3582761 _91854 y x z) (@lem3582783 _91854 y x z)). Qed.
Lemma lem3582786 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3582787 (x : Prop) : (x = x) = True.
Proof. exact (@lem3582786 Prop x). Qed.
Lemma lem3582788 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : ((term395 _91854 y x z) = (term395 _91854 y x z)) = True.
Proof. exact (@lem3582787 (term395 _91854 y x z)). Qed.
Lemma lem3582789 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : ((term373 _91854 x y z) = (term395 _91854 y x z)) = True.
Proof. exact (TRANS (@lem3582784 _91854 y x z) (@lem3582788 _91854 y x z)). Qed.
Lemma lem3582790 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : True = ((term373 _91854 x y z) = (term395 _91854 y x z)).
Proof. exact (SYM (@lem3582789 _91854 y x z)). Qed.
Lemma lem3582791 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term373 _91854 x y z) = (term395 _91854 y x z).
Proof. exact (EQ_MP (@lem3582790 _91854 y x z) (@lem0)). Qed.
Lemma lem3582792 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : term395 _91854 y x z.
Proof. exact (EQ_MP (@lem3582791 _91854 y x z) (@lem3582625 _91854 x y z)). Qed.
Lemma lem3582794 (b : Prop) (a : Prop) : (a \/ b) = (term380 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3582795 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : (term395 _91854 y x z) = (term398 _91854 x y z).
Proof. exact (@lem3582794 (term399 _91854 y x z) (y = z)). Qed.
Lemma lem3582797 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3582798 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term402 _91854 y x z) = (term403 _91854 y x z).
Proof. exact (@lem3582797 (term391 _91854 x y) (term391 _91854 x z)). Qed.
Lemma lem3582800 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3582801 {_91854 : Type'} (x : _91854) (y : _91854) : (term404 _91854 x y) = (x = y).
Proof. exact (@lem3582800 (x = y)). Qed.
Lemma lem3582802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3582803 {_91854 : Type'} (x : _91854) (y : _91854) : (term405 _91854 x y) = (term406 _91854 x y).
Proof. exact (MK_COMB (@lem3582802) (@lem3582801 _91854 x y)). Qed.
Lemma lem3582805 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3582806 {_91854 : Type'} (x : _91854) (z : _91854) : (term404 _91854 x z) = (x = z).
Proof. exact (@lem3582805 (x = z)). Qed.
Lemma lem3582807 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term403 _91854 y x z) = (term407 _91854 y x z).
Proof. exact (MK_COMB (@lem3582803 _91854 x y) (@lem3582806 _91854 x z)). Qed.
Lemma lem3582808 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term402 _91854 y x z) = (term407 _91854 y x z).
Proof. exact (TRANS (@lem3582798 _91854 y x z) (@lem3582807 _91854 y x z)). Qed.
Lemma lem3582809 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3582810 {_91854 : Type'} (y : _91854) (x : _91854) (z : _91854) : (term408 _91854 y x z) = (term409 _91854 y x z).
Proof. exact (MK_COMB (@lem3582809) (@lem3582808 _91854 y x z)). Qed.
Lemma lem3582811 {_91854 : Type'} (y : _91854) (z : _91854) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3582812 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : (term398 _91854 x y z) = (term410 _91854 x y z).
Proof. exact (MK_COMB (@lem3582810 _91854 y x z) (@lem3582811 _91854 y z)). Qed.
Lemma lem3582813 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : (term395 _91854 y x z) = (term410 _91854 x y z).
Proof. exact (TRANS (@lem3582795 _91854 x y z) (@lem3582812 _91854 x y z)). Qed.
Lemma lem3582815 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term424 _91854 _91858 _91859 g h f x.
Proof. exact (conj (@lem3582693 _91854 _91858 _91859 x P f g h h1) (@lem3582702 _91854 _91859 f x)). Qed.
Lemma lem3582817 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : term410 _91854 x y z.
Proof. exact (EQ_MP (@lem3582813 _91854 x y z) (@lem3582792 _91854 y x z)). Qed.
Lemma lem3582818 {_91854 : Type'} (x : _91854) (y : _91854) (z : _91854) : term410 _91854 x y z.
Proof. exact (@lem3582817 _91854 x y z). Qed.
Lemma lem3582819 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (h : _91859 -> _91858) (f : _91859 -> _91854) (x : _91859) : term425 _91854 _91858 _91859 g h f x.
Proof. exact (@lem3582818 _91854 (f x) (term377 _91854 _91858 _91859 g h x) (f x)). Qed.
Lemma lem3582822 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : (term377 _91854 _91858 _91859 g h x) = (f x).
Proof. exact (@lem3582819 _91854 _91858 _91859 g h f x (@lem3582815 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582823 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term385 _91854 _91858 _91859 g h f x.
Proof. exact (fun h0 : term386 _91854 _91858 _91859 g h f x => @lem3582822 _91854 _91858 _91859 x P f g h h1). Qed.
Lemma lem3582825 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582826 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (h : _91859 -> _91858) (f : _91859 -> _91854) (x : _91859) : (term385 _91854 _91858 _91859 g h f x) = ((term377 _91854 _91858 _91859 g h x) = (f x)).
Proof. exact (@lem3582825 ((term377 _91854 _91858 _91859 g h x) = (f x))). Qed.
Lemma lem3582827 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : (term377 _91854 _91858 _91859 g h x) = (f x).
Proof. exact (EQ_MP (@lem3582826 _91854 _91858 _91859 g h f x) (@lem3582823 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582830 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3582832 {_91854 _91858 _91859 : Type'} (g : _91858 -> _91854) (_38664 : _91858) (f : _91859 -> _91854) (x : _91859) : (term70 _91854 _91858 _91859 g _38664 f x) = (term426 _91854 _91858 _91859 g _38664 f x).
Proof. exact (@lem3582830 ((g _38664) = (f x))). Qed.
Lemma lem3582835 {_91854 _91858 _91859 : Type'} (_38664 : _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term426 _91854 _91858 _91859 g _38664 f x.
Proof. exact (EQ_MP (@lem3582832 _91854 _91858 _91859 g _38664 f x) (@lem3582329 _91854 _91858 _91859 _38664 x P f g h h1)). Qed.
Lemma lem3582836 {_91854 _91858 _91859 : Type'} (_38664 : _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term426 _91854 _91858 _91859 g _38664 f x.
Proof. exact (@lem3582835 _91854 _91858 _91859 _38664 x P f g h h1). Qed.
Lemma lem3582837 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term427 _91854 _91858 _91859 g h f x.
Proof. exact (@lem3582836 _91854 _91858 _91859 (h x) x P f g h h1). Qed.
Lemma lem3582840 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : False.
Proof. exact (@lem3582837 _91854 _91858 _91859 x P f g h h1 (@lem3582827 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582841 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : term417.
Proof. exact (fun h0 : ~ False => @lem3582840 _91854 _91858 _91859 x P f g h h1). Qed.
Lemma lem3582843 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3582844 : term417 = False.
Proof. exact (@lem3582843 False). Qed.
Lemma lem3582845 {_91854 _91858 _91859 : Type'} (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term308 _91854 _91858 _91859 x P f g h) : False.
Proof. exact (EQ_MP (@lem3582844) (@lem3582841 _91854 _91858 _91859 x P f g h h1)). Qed.
Lemma lem3582846 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term362 _91854 _91858 _91859 y x P f g h) : False.
Proof. exact (or_elim (@lem3582239 _91854 _91858 _91859 y x P f g h h1) (fun h0 : term248 _91854 _91858 _91859 y P f x g => @lem3582587 _91854 _91858 _91859 y P f x g h0) (fun h0 : term308 _91854 _91858 _91859 x P f g h => @lem3582845 _91854 _91858 _91859 x P f g h h0)). Qed.
Lemma lem3582847 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term362 _91854 _91858 _91859 y x P f g h) : (term362 _91854 _91858 _91859 y x P f g h) = False.
Proof. exact (prop_ext (fun h2 : term362 _91854 _91858 _91859 y x P f g h => @lem3582846 _91854 _91858 _91859 y x P f g h h1) (fun h2 : False => @lem3582239 _91854 _91858 _91859 y x P f g h h1)). Qed.
Lemma lem3582848 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h : _91859 -> _91858) (h1 : term362 _91854 _91858 _91859 y x P f g h) : False.
Proof. exact (EQ_MP (@lem3582847 _91854 _91858 _91859 y x P f g h h1) (@lem3582239 _91854 _91858 _91859 y x P f g h h1)). Qed.
Lemma lem3582849 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (x : _91859) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h1 : term365 _91854 _91858 _91859 y x P f g) : False.
Proof. exact (ex_elim (@lem3582144 _91854 _91858 _91859 y x P f g h1) (fun h : _91859 -> _91858 => fun h0 : term364 _91854 _91858 _91859 y x P f g h => @lem3582848 _91854 _91858 _91859 y x P f g h h0)). Qed.
Lemma lem3582850 {_91854 _91858 _91859 : Type'} (y : _91859 -> _91858) (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h1 : term367 _91854 _91858 _91859 y P f g) : False.
Proof. exact (ex_elim (@lem3582143 _91854 _91858 _91859 y P f g h1) (fun x : _91859 => fun h0 : term366 _91854 _91858 _91859 y P f g x => @lem3582849 _91854 _91858 _91859 y x P f g h0)). Qed.
Lemma lem3582851 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h1 : term63 _91854 _91858 _91859 P f g) : False.
Proof. exact (ex_elim (@lem3582142 _91854 _91858 _91859 P f g h1) (fun y : _91859 -> _91858 => fun h0 : term368 _91854 _91858 _91859 P f g y => @lem3582850 _91854 _91858 _91859 y P f g h0)). Qed.
Lemma lem3582852 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h1 : term63 _91854 _91858 _91859 P f g) : (term63 _91854 _91858 _91859 P f g) = False.
Proof. exact (prop_ext (fun h2 : term63 _91854 _91858 _91859 P f g => @lem3582851 _91854 _91858 _91859 P f g h1) (fun h2 : False => @lem3581490 _91854 _91858 _91859 P f g h1)). Qed.
Lemma lem3582853 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) (h1 : term63 _91854 _91858 _91859 P f g) : False.
Proof. exact (EQ_MP (@lem3582852 _91854 _91858 _91859 P f g h1) (@lem3581490 _91854 _91858 _91859 P f g h1)). Qed.
Lemma lem3582854 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : term62 _91854 _91858 _91859 P f g.
Proof. exact (fun h0 : term63 _91854 _91858 _91859 P f g => @lem3582853 _91854 _91858 _91859 P f g h0). Qed.
Lemma lem3582855 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) (g : _91858 -> _91854) : (term36 _91854 _91858 _91859 P g f) = (term34 _91854 _91858 _91859 P f g).
Proof. exact (EQ_MP (@lem3581489 _91854 _91858 _91859 P f g) (@lem3582854 _91854 _91858 _91859 P f g)). Qed.
Lemma lem3582860 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) (f : _91859 -> _91854) : term40 _91854 _91858 _91859 P f.
Proof. exact (fun g : _91858 -> _91854 => @lem3582855 _91854 _91858 _91859 P f g). Qed.
Lemma lem3582865 {_91854 _91858 _91859 : Type'} (P : _91859 -> Prop) : term44 _91854 _91858 _91859 P.
Proof. exact (fun f : _91859 -> _91854 => @lem3582860 _91854 _91858 _91859 P f). Qed.
Lemma lem3582870 {_91854 _91858 _91859 : Type'} : term48 _91854 _91858 _91859.
Proof. exact (fun P : _91859 -> Prop => @lem3582865 _91854 _91858 _91859 P). Qed.
Lemma lem3582871 {_91854 _91858 _91859 : Type'} : term50 _91854 _91858 _91859.
Proof. exact (EQ_MP (@lem3581485 _91854 _91858 _91859) (@lem3582870 _91854 _91858 _91859)). Qed.
Lemma lem3582873 {_91854 _91858 _91859 : Type'} : term50 _91854 _91858 _91859.
Proof. exact (@lem3581358 _91854 _91858 _91859 (@lem3582871 _91854 _91858 _91859)). Qed.
Lemma lem3582874 {_91854 _91858 _91859 : Type'} (h1 : term51 _91854 _91858 _91859) : False.
Proof. exact (@lem3582873 _91854 _91858 _91859 (@lem3581342 _91854 _91858 _91859 h1)). Qed.
Lemma lem3582875 {_91854 _91858 _91859 : Type'} (h1 : term51 _91854 _91858 _91859) : (term51 _91854 _91858 _91859) = False.
Proof. exact (prop_ext (fun h2 : term51 _91854 _91858 _91859 => @lem3582874 _91854 _91858 _91859 h1) (fun h2 : False => @lem3581342 _91854 _91858 _91859 h1)). Qed.
Lemma lem3582876 {_91854 _91858 _91859 : Type'} (h1 : term51 _91854 _91858 _91859) : False.
Proof. exact (EQ_MP (@lem3582875 _91854 _91858 _91859 h1) (@lem3581342 _91854 _91858 _91859 h1)). Qed.
Lemma lem3582877 {_91854 _91858 _91859 : Type'} : term50 _91854 _91858 _91859.
Proof. exact (fun h0 : term51 _91854 _91858 _91859 => @lem3582876 _91854 _91858 _91859 h0). Qed.
Lemma lem3582878 {_91854 _91858 _91859 : Type'} : term48 _91854 _91858 _91859.
Proof. exact (EQ_MP (@lem3581341 _91854 _91858 _91859) (@lem3582877 _91854 _91858 _91859)). Qed.
Lemma lem3582879 {_91854 _91858 _91859 : Type'} : term47 _91854 _91858 _91859.
Proof. exact (EQ_MP (@lem3581337 _91854 _91858 _91859) (@lem3582878 _91854 _91858 _91859)). Qed.
