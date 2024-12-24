Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_OPTION_THM_term_abbrevs.
Require Import FORALL_OPTION_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem1072236 {_24424 : Type'} (P : type1160 _24424) : term0 _24424 P.
Proof. exact (@lem1072225 _24424 P). Qed.
Lemma lem1072237 {_24424 : Type'} (P : type1160 _24424) : (term0 _24424 P) = ((term1 _24424 P) = (term2 _24424 P)).
Proof. exact (eq_refl (term0 _24424 P)). Qed.
Lemma lem1072250 (p : Prop) : p = (term3 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1072251 {_24440 : Type'} (P : _24440 -> Prop) : ((term4 _24440 P) = (term5 _24440 P)) = (term6 _24440 P).
Proof. exact (@lem1072250 ((term4 _24440 P) = (term5 _24440 P))). Qed.
Lemma lem1072252 {_24440 : Type'} (P : _24440 -> Prop) : (term6 _24440 P) = ((term4 _24440 P) = (term5 _24440 P)).
Proof. exact (SYM (@lem1072251 _24440 P)). Qed.
Lemma lem1072253 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term7 _24440 P) : term7 _24440 P.
Proof. exact (h1). Qed.
Lemma lem1072256 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term6 _24440 P) : term6 _24440 P.
Proof. exact (h1). Qed.
Lemma lem1072257 {_24440 : Type'} (P : _24440 -> Prop) : term8 _24440 P.
Proof. exact (fun h0 : term6 _24440 P => @lem1072256 _24440 P h0). Qed.
Lemma lem1072258 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term8 _24440 P) : term8 _24440 P.
Proof. exact (h1). Qed.
Lemma lem1072259 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term6 _24440 P) : term6 _24440 P.
Proof. exact (h1). Qed.
Lemma lem1072260 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term6 _24440 P) (h2 : term8 _24440 P) : term6 _24440 P.
Proof. exact (@lem1072258 _24440 P h2 (@lem1072259 _24440 P h1)). Qed.
Lemma lem1072261 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term6 _24440 P) : term9 _24440 P.
Proof. exact (fun h0 : term8 _24440 P => @lem1072260 _24440 P h1 h0). Qed.
Lemma lem1072262 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term8 _24440 P) : term8 _24440 P.
Proof. exact (h1). Qed.
Lemma lem1072263 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term6 _24440 P) (h2 : term8 _24440 P) : term6 _24440 P.
Proof. exact (@lem1072261 _24440 P h1 (@lem1072262 _24440 P h2)). Qed.
Lemma lem1072264 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term8 _24440 P) : term8 _24440 P.
Proof. exact (fun h0 : term6 _24440 P => @lem1072263 _24440 P h0 h1). Qed.
Lemma lem1072265 {_24440 : Type'} (P : _24440 -> Prop) : term10 _24440 P.
Proof. exact (fun h0 : term8 _24440 P => @lem1072264 _24440 P h0). Qed.
Lemma lem1072268 {_24440 : Type'} (P : _24440 -> Prop) : term8 _24440 P.
Proof. exact (@lem1072265 _24440 P (@lem1072257 _24440 P)). Qed.
Lemma lem1072269 {_24440 : Type'} (P : _24440 -> Prop) : term8 _24440 P.
Proof. exact (@lem1072268 _24440 P). Qed.
Lemma lem1072275 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1072276 {_24440 : Type'} (P : _24440 -> Prop) : (term6 _24440 P) = (term11 _24440 P).
Proof. exact (@lem1072275 (term7 _24440 P)). Qed.
Lemma lem1072278 (t : Prop) : (term12 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1072279 {_24440 : Type'} (P : _24440 -> Prop) : (term11 _24440 P) = ((term4 _24440 P) = (term5 _24440 P)).
Proof. exact (@lem1072278 ((term4 _24440 P) = (term5 _24440 P))). Qed.
Lemma lem1072280 {_24440 : Type'} (P : _24440 -> Prop) : (term6 _24440 P) = ((term4 _24440 P) = (term5 _24440 P)).
Proof. exact (TRANS (@lem1072276 _24440 P) (@lem1072279 _24440 P)). Qed.
Lemma lem1072289 {_24440 : Type'} : (term13 _24440) = (term14 _24440).
Proof. exact (fun_ext (fun P : _24440 -> Prop => @lem1072280 _24440 P)). Qed.
Lemma lem1072290 {_24440 : Type'} : (@all (_24440 -> Prop)) = (@all (_24440 -> Prop)).
Proof. exact (eq_refl (@all (_24440 -> Prop))). Qed.
Lemma lem1072299 {_24440 : Type'} : (term15 _24440) = (term16 _24440).
Proof. exact (MK_COMB (@lem1072290 _24440) (@lem1072289 _24440)). Qed.
Lemma lem1072302 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term17 _24440 P x) = (term17 _24440 P x).
Proof. exact (eq_refl (term17 _24440 P x)). Qed.
Lemma lem1072303 {_24440 : Type'} (P : _24440 -> Prop) : (term18 _24440 P) = (term18 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072302 _24440 P x)). Qed.
Lemma lem1072304 {_24440 : Type'} : (@all _24440) = (@all _24440).
Proof. exact (eq_refl (@all _24440)). Qed.
Lemma lem1072305 {_24440 : Type'} (P : _24440 -> Prop) : (term19 _24440 P) = (term19 _24440 P).
Proof. exact (MK_COMB (@lem1072304 _24440) (@lem1072303 _24440 P)). Qed.
Lemma lem1072306 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072307 {_24440 : Type'} (P : _24440 -> Prop) : (term5 _24440 P) = (term5 _24440 P).
Proof. exact (MK_COMB (@lem1072306) (@lem1072305 _24440 P)). Qed.
Lemma lem1072308 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1072309 {_24440 : Type'} (P : _24440 -> Prop) : (term20 _24440 P) = (term20 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072308 _24440 P x)). Qed.
Lemma lem1072310 {_24440 : Type'} : (@ex _24440) = (@ex _24440).
Proof. exact (eq_refl (@ex _24440)). Qed.
Lemma lem1072311 {_24440 : Type'} (P : _24440 -> Prop) : (term4 _24440 P) = (term4 _24440 P).
Proof. exact (MK_COMB (@lem1072310 _24440) (@lem1072309 _24440 P)). Qed.
Lemma lem1072312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072313 {_24440 : Type'} (P : _24440 -> Prop) : (term21 _24440 P) = (term21 _24440 P).
Proof. exact (MK_COMB (@lem1072312) (@lem1072311 _24440 P)). Qed.
Lemma lem1072314 {_24440 : Type'} (P : _24440 -> Prop) : ((term4 _24440 P) = (term5 _24440 P)) = ((term4 _24440 P) = (term5 _24440 P)).
Proof. exact (MK_COMB (@lem1072313 _24440 P) (@lem1072307 _24440 P)). Qed.
Lemma lem1072315 {_24440 : Type'} : (term14 _24440) = (term14 _24440).
Proof. exact (fun_ext (fun P : _24440 -> Prop => @lem1072314 _24440 P)). Qed.
Lemma lem1072316 {_24440 : Type'} : (@all (_24440 -> Prop)) = (@all (_24440 -> Prop)).
Proof. exact (eq_refl (@all (_24440 -> Prop))). Qed.
Lemma lem1072317 {_24440 : Type'} : (term16 _24440) = (term16 _24440).
Proof. exact (MK_COMB (@lem1072316 _24440) (@lem1072315 _24440)). Qed.
Lemma lem1072338 {_24440 : Type'} : (term15 _24440) = (term16 _24440).
Proof. exact (TRANS (@lem1072299 _24440) (@lem1072317 _24440)). Qed.
Lemma lem1072339 {_24440 : Type'} : (term16 _24440) = (term15 _24440).
Proof. exact (SYM (@lem1072338 _24440)). Qed.
Lemma lem1072341 (p : Prop) : p = (term3 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1072342 {_24440 : Type'} (P : _24440 -> Prop) : ((term4 _24440 P) = (term5 _24440 P)) = (term6 _24440 P).
Proof. exact (@lem1072341 ((term4 _24440 P) = (term5 _24440 P))). Qed.
Lemma lem1072343 {_24440 : Type'} (P : _24440 -> Prop) : (term6 _24440 P) = ((term4 _24440 P) = (term5 _24440 P)).
Proof. exact (SYM (@lem1072342 _24440 P)). Qed.
Lemma lem1072344 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term7 _24440 P) : term7 _24440 P.
Proof. exact (h1). Qed.
Lemma lem1072346 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1072347 {_24440 : Type'} (P : _24440 -> Prop) : (term22 _24440 P) = (term19 _24440 P).
Proof. exact (@lem18394 _24440 P). Qed.
Lemma lem1072348 {_24440 : Type'} (P : _24440 -> Prop) : (term23 _24440 P) = (term24 _24440 P).
Proof. exact (@lem1072347 _24440 (term20 _24440 P)). Qed.
Lemma lem1072349 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term25 _24440 P x) = (P x).
Proof. exact (eq_refl (term25 _24440 P x)). Qed.
Lemma lem1072350 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072352 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term26 _24440 P x) = (term17 _24440 P x).
Proof. exact (MK_COMB (@lem1072350) (@lem1072349 _24440 P x)). Qed.
Lemma lem1072353 {_24440 : Type'} (P : _24440 -> Prop) : (term27 _24440 P) = (term18 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072352 _24440 P x)). Qed.
Lemma lem1072354 {_24440 : Type'} : (@all _24440) = (@all _24440).
Proof. exact (eq_refl (@all _24440)). Qed.
Lemma lem1072355 {_24440 : Type'} (P : _24440 -> Prop) : (term24 _24440 P) = (term19 _24440 P).
Proof. exact (MK_COMB (@lem1072354 _24440) (@lem1072353 _24440 P)). Qed.
Lemma lem1072356 {_24440 : Type'} (P : _24440 -> Prop) : (term23 _24440 P) = (term19 _24440 P).
Proof. exact (TRANS (@lem1072348 _24440 P) (@lem1072355 _24440 P)). Qed.
Lemma lem1072357 {_24440 : Type'} (P : _24440 -> Prop) : (term20 _24440 P) = (term20 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072346 _24440 P x)). Qed.
Lemma lem1072358 {_24440 : Type'} : (@ex _24440) = (@ex _24440).
Proof. exact (eq_refl (@ex _24440)). Qed.
Lemma lem1072359 {_24440 : Type'} (P : _24440 -> Prop) : (term4 _24440 P) = (term4 _24440 P).
Proof. exact (MK_COMB (@lem1072358 _24440) (@lem1072357 _24440 P)). Qed.
Lemma lem1072360 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term17 _24440 P x) = (term17 _24440 P x).
Proof. exact (eq_refl (term17 _24440 P x)). Qed.
Lemma lem1072363 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term28 _24440 P x) = (P x).
Proof. exact (@lem16933 (P x)). Qed.
Lemma lem1072364 {_24440 : Type'} (P : _24440 -> Prop) : (term29 _24440 P) = (term30 _24440 P).
Proof. exact (@lem18392 _24440 P). Qed.
Lemma lem1072365 {_24440 : Type'} (P : _24440 -> Prop) : (term5 _24440 P) = (term31 _24440 P).
Proof. exact (@lem1072364 _24440 (term18 _24440 P)). Qed.
Lemma lem1072366 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term32 _24440 P x) = (term17 _24440 P x).
Proof. exact (eq_refl (term32 _24440 P x)). Qed.
Lemma lem1072367 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072368 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term33 _24440 P x) = (term28 _24440 P x).
Proof. exact (MK_COMB (@lem1072367) (@lem1072366 _24440 P x)). Qed.
Lemma lem1072369 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term33 _24440 P x) = (P x).
Proof. exact (TRANS (@lem1072368 _24440 P x) (@lem1072363 _24440 P x)). Qed.
Lemma lem1072370 {_24440 : Type'} (P : _24440 -> Prop) : (term34 _24440 P) = (term20 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072369 _24440 P x)). Qed.
Lemma lem1072371 {_24440 : Type'} : (@ex _24440) = (@ex _24440).
Proof. exact (eq_refl (@ex _24440)). Qed.
Lemma lem1072372 {_24440 : Type'} (P : _24440 -> Prop) : (term31 _24440 P) = (term4 _24440 P).
Proof. exact (MK_COMB (@lem1072371 _24440) (@lem1072370 _24440 P)). Qed.
Lemma lem1072373 {_24440 : Type'} (P : _24440 -> Prop) : (term5 _24440 P) = (term4 _24440 P).
Proof. exact (TRANS (@lem1072365 _24440 P) (@lem1072372 _24440 P)). Qed.
Lemma lem1072374 {_24440 : Type'} (P : _24440 -> Prop) : (term18 _24440 P) = (term18 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072360 _24440 P x)). Qed.
Lemma lem1072375 {_24440 : Type'} : (@all _24440) = (@all _24440).
Proof. exact (eq_refl (@all _24440)). Qed.
Lemma lem1072376 {_24440 : Type'} (P : _24440 -> Prop) : (term19 _24440 P) = (term19 _24440 P).
Proof. exact (MK_COMB (@lem1072375 _24440) (@lem1072374 _24440 P)). Qed.
Lemma lem1072377 {_24440 : Type'} (P : _24440 -> Prop) : (term35 _24440 P) = (term19 _24440 P).
Proof. exact (@lem16933 (term19 _24440 P)). Qed.
Lemma lem1072378 {_24440 : Type'} (P : _24440 -> Prop) : (term35 _24440 P) = (term19 _24440 P).
Proof. exact (TRANS (@lem1072377 _24440 P) (@lem1072376 _24440 P)). Qed.
Lemma lem1072379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072380 {_24440 : Type'} (P : _24440 -> Prop) : (term36 _24440 P) = (term37 _24440 P).
Proof. exact (MK_COMB (@lem1072379) (@lem1072356 _24440 P)). Qed.
Lemma lem1072381 {_24440 : Type'} (P : _24440 -> Prop) : (term38 _24440 P) = (term39 _24440 P).
Proof. exact (MK_COMB (@lem1072380 _24440 P) (@lem1072373 _24440 P)). Qed.
Lemma lem1072382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072383 {_24440 : Type'} (P : _24440 -> Prop) : (term40 _24440 P) = (term40 _24440 P).
Proof. exact (MK_COMB (@lem1072382) (@lem1072359 _24440 P)). Qed.
Lemma lem1072384 {_24440 : Type'} (P : _24440 -> Prop) : (term41 _24440 P) = (term42 _24440 P).
Proof. exact (MK_COMB (@lem1072383 _24440 P) (@lem1072378 _24440 P)). Qed.
Lemma lem1072385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1072386 {_24440 : Type'} (P : _24440 -> Prop) : (term43 _24440 P) = (term44 _24440 P).
Proof. exact (MK_COMB (@lem1072385) (@lem1072384 _24440 P)). Qed.
Lemma lem1072387 {_24440 : Type'} (P : _24440 -> Prop) : (term45 _24440 P) = (term46 _24440 P).
Proof. exact (MK_COMB (@lem1072386 _24440 P) (@lem1072381 _24440 P)). Qed.
Lemma lem1072388 {_24440 : Type'} (P : _24440 -> Prop) : (term7 _24440 P) = (term45 _24440 P).
Proof. exact (@lem17646 (term4 _24440 P) (term5 _24440 P)). Qed.
Lemma lem1072389 {_24440 : Type'} (P : _24440 -> Prop) : (term7 _24440 P) = (term46 _24440 P).
Proof. exact (TRANS (@lem1072388 _24440 P) (@lem1072387 _24440 P)). Qed.
Lemma lem1072408 {A : Type'} (P : A -> Prop) (Q : Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1072409 {_24440 : Type'} (P : _24440 -> Prop) (Q : Prop) : (term47 _24440 P Q) = (term48 _24440 P Q).
Proof. exact (@lem1072408 _24440 P Q). Qed.
Lemma lem1072410 {_24440 : Type'} (P : _24440 -> Prop) : (term42 _24440 P) = (term49 _24440 P).
Proof. exact (@lem1072409 _24440 P (term19 _24440 P)). Qed.
Lemma lem1072411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1072412 {_24440 : Type'} (P : _24440 -> Prop) : (term44 _24440 P) = (term50 _24440 P).
Proof. exact (MK_COMB (@lem1072411) (@lem1072410 _24440 P)). Qed.
Lemma lem1072414 {A : Type'} (P : Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1072415 {_24440 : Type'} (P : Prop) (Q : _24440 -> Prop) : (term51 _24440 P Q) = (term52 _24440 P Q).
Proof. exact (@lem1072414 _24440 P Q). Qed.
Lemma lem1072416 {_24440 : Type'} (P : _24440 -> Prop) : (term39 _24440 P) = (term53 _24440 P).
Proof. exact (@lem1072415 _24440 (term19 _24440 P) P). Qed.
Lemma lem1072417 {_24440 : Type'} (P : _24440 -> Prop) : (term46 _24440 P) = (term54 _24440 P).
Proof. exact (MK_COMB (@lem1072412 _24440 P) (@lem1072416 _24440 P)). Qed.
Lemma lem1072419 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1072420 {_24440 : Type'} (P : _24440 -> Prop) (Q : _24440 -> Prop) : (term55 _24440 P Q) = (term56 _24440 P Q).
Proof. exact (@lem1072419 _24440 P Q). Qed.
Lemma lem1072421 {_24440 : Type'} (P : _24440 -> Prop) : (term57 _24440 P) = (term58 _24440 P).
Proof. exact (@lem1072420 _24440 (term59 _24440 P) (term60 _24440 P)). Qed.
Lemma lem1072422 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) : (term61 _24440 P x) = (term62 _24440 x P).
Proof. exact (eq_refl (term61 _24440 P x)). Qed.
Lemma lem1072423 {_24440 : Type'} (P : _24440 -> Prop) : (term63 _24440 P) = (term59 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072422 _24440 x P)). Qed.
Lemma lem1072424 {_24440 : Type'} : (@ex _24440) = (@ex _24440).
Proof. exact (eq_refl (@ex _24440)). Qed.
Lemma lem1072425 {_24440 : Type'} (P : _24440 -> Prop) : (term64 _24440 P) = (term49 _24440 P).
Proof. exact (MK_COMB (@lem1072424 _24440) (@lem1072423 _24440 P)). Qed.
Lemma lem1072426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1072427 {_24440 : Type'} (P : _24440 -> Prop) : (term65 _24440 P) = (term50 _24440 P).
Proof. exact (MK_COMB (@lem1072426) (@lem1072425 _24440 P)). Qed.
Lemma lem1072428 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term66 _24440 P x) = (term67 _24440 P x).
Proof. exact (eq_refl (term66 _24440 P x)). Qed.
Lemma lem1072429 {_24440 : Type'} (P : _24440 -> Prop) : (term68 _24440 P) = (term60 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072428 _24440 P x)). Qed.
Lemma lem1072430 {_24440 : Type'} : (@ex _24440) = (@ex _24440).
Proof. exact (eq_refl (@ex _24440)). Qed.
Lemma lem1072431 {_24440 : Type'} (P : _24440 -> Prop) : (term69 _24440 P) = (term53 _24440 P).
Proof. exact (MK_COMB (@lem1072430 _24440) (@lem1072429 _24440 P)). Qed.
Lemma lem1072432 {_24440 : Type'} (P : _24440 -> Prop) : (term57 _24440 P) = (term54 _24440 P).
Proof. exact (MK_COMB (@lem1072427 _24440 P) (@lem1072431 _24440 P)). Qed.
Lemma lem1072433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072434 {_24440 : Type'} (P : _24440 -> Prop) : (term70 _24440 P) = (term71 _24440 P).
Proof. exact (MK_COMB (@lem1072433) (@lem1072432 _24440 P)). Qed.
Lemma lem1072435 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) : (term61 _24440 P x) = (term62 _24440 x P).
Proof. exact (eq_refl (term61 _24440 P x)). Qed.
Lemma lem1072436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1072437 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) : (term72 _24440 P x) = (term73 _24440 x P).
Proof. exact (MK_COMB (@lem1072436) (@lem1072435 _24440 x P)). Qed.
Lemma lem1072438 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term66 _24440 P x) = (term67 _24440 P x).
Proof. exact (eq_refl (term66 _24440 P x)). Qed.
Lemma lem1072439 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term74 _24440 P x) = (term75 _24440 P x).
Proof. exact (MK_COMB (@lem1072437 _24440 x P) (@lem1072438 _24440 P x)). Qed.
Lemma lem1072440 {_24440 : Type'} (P : _24440 -> Prop) : (term76 _24440 P) = (term77 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072439 _24440 P x)). Qed.
Lemma lem1072441 {_24440 : Type'} : (@ex _24440) = (@ex _24440).
Proof. exact (eq_refl (@ex _24440)). Qed.
Lemma lem1072442 {_24440 : Type'} (P : _24440 -> Prop) : (term58 _24440 P) = (term78 _24440 P).
Proof. exact (MK_COMB (@lem1072441 _24440) (@lem1072440 _24440 P)). Qed.
Lemma lem1072443 {_24440 : Type'} (P : _24440 -> Prop) : ((term57 _24440 P) = (term58 _24440 P)) = ((term54 _24440 P) = (term78 _24440 P)).
Proof. exact (MK_COMB (@lem1072434 _24440 P) (@lem1072442 _24440 P)). Qed.
Lemma lem1072444 {_24440 : Type'} (P : _24440 -> Prop) : (term54 _24440 P) = (term78 _24440 P).
Proof. exact (EQ_MP (@lem1072443 _24440 P) (@lem1072421 _24440 P)). Qed.
Lemma lem1072446 {_24440 : Type'} (P : _24440 -> Prop) : (term46 _24440 P) = (term78 _24440 P).
Proof. exact (TRANS (@lem1072417 _24440 P) (@lem1072444 _24440 P)). Qed.
Lemma lem1072447 {_24440 : Type'} (P : _24440 -> Prop) : (term7 _24440 P) = (term78 _24440 P).
Proof. exact (TRANS (@lem1072389 _24440 P) (@lem1072446 _24440 P)). Qed.
Lemma lem1072448 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term7 _24440 P) : term78 _24440 P.
Proof. exact (EQ_MP (@lem1072447 _24440 P) (@lem1072344 _24440 P h1)). Qed.
Lemma lem1072449 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term75 _24440 P x) : term75 _24440 P x.
Proof. exact (h1). Qed.
Lemma lem1072452 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1072457 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term17 _24440 P x) = (term17 _24440 P x).
Proof. exact (eq_refl (term17 _24440 P x)). Qed.
Lemma lem1072458 {_24440 : Type'} (P : _24440 -> Prop) : (term18 _24440 P) = (term18 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072457 _24440 P x)). Qed.
Lemma lem1072459 {_24440 : Type'} : (@all _24440) = (@all _24440).
Proof. exact (eq_refl (@all _24440)). Qed.
Lemma lem1072460 {_24440 : Type'} (P : _24440 -> Prop) : (term19 _24440 P) = (term19 _24440 P).
Proof. exact (MK_COMB (@lem1072459 _24440) (@lem1072458 _24440 P)). Qed.
Lemma lem1072461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072462 {_24440 : Type'} (P : _24440 -> Prop) : (term37 _24440 P) = (term37 _24440 P).
Proof. exact (MK_COMB (@lem1072461) (@lem1072460 _24440 P)). Qed.
Lemma lem1072463 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term67 _24440 P x) = (term67 _24440 P x).
Proof. exact (MK_COMB (@lem1072462 _24440 P) (@lem1072452 _24440 P x)). Qed.
Lemma lem1072468 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term17 _24440 P x) = (term17 _24440 P x).
Proof. exact (eq_refl (term17 _24440 P x)). Qed.
Lemma lem1072469 {_24440 : Type'} (P : _24440 -> Prop) : (term18 _24440 P) = (term18 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072468 _24440 P x)). Qed.
Lemma lem1072470 {_24440 : Type'} : (@all _24440) = (@all _24440).
Proof. exact (eq_refl (@all _24440)). Qed.
Lemma lem1072471 {_24440 : Type'} (P : _24440 -> Prop) : (term19 _24440 P) = (term19 _24440 P).
Proof. exact (MK_COMB (@lem1072470 _24440) (@lem1072469 _24440 P)). Qed.
Lemma lem1072476 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term79 _24440 P x) = (term79 _24440 P x).
Proof. exact (eq_refl (term79 _24440 P x)). Qed.
Lemma lem1072477 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) : (term62 _24440 x P) = (term62 _24440 x P).
Proof. exact (MK_COMB (@lem1072476 _24440 P x) (@lem1072471 _24440 P)). Qed.
Lemma lem1072478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1072479 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) : (term73 _24440 x P) = (term73 _24440 x P).
Proof. exact (MK_COMB (@lem1072478) (@lem1072477 _24440 x P)). Qed.
Lemma lem1072480 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term75 _24440 P x) = (term75 _24440 P x).
Proof. exact (MK_COMB (@lem1072479 _24440 x P) (@lem1072463 _24440 P x)). Qed.
Lemma lem1072481 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term75 _24440 P x) : term75 _24440 P x.
Proof. exact (EQ_MP (@lem1072480 _24440 P x) (@lem1072449 _24440 P x h1)). Qed.
Lemma lem1072482 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term62 _24440 x P.
Proof. exact (h1). Qed.
Lemma lem1072483 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term67 _24440 P x.
Proof. exact (h1). Qed.
Lemma lem1072484 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term19 _24440 P.
Proof. exact (proj2 (@lem1072482 _24440 x P h1)). Qed.
Lemma lem1072487 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term19 _24440 P.
Proof. exact (proj1 (@lem1072483 _24440 P x h1)). Qed.
Lemma lem1072493 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term17 _24440 P x) = (term17 _24440 P x).
Proof. exact (eq_refl (term17 _24440 P x)). Qed.
Lemma lem1072494 {_24440 : Type'} (P : _24440 -> Prop) : (term18 _24440 P) = (term18 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072493 _24440 P x)). Qed.
Lemma lem1072495 {_24440 : Type'} : (@all _24440) = (@all _24440).
Proof. exact (eq_refl (@all _24440)). Qed.
Lemma lem1072497 {_24440 : Type'} (P : _24440 -> Prop) : (term19 _24440 P) = (term19 _24440 P).
Proof. exact (MK_COMB (@lem1072495 _24440) (@lem1072494 _24440 P)). Qed.
Lemma lem1072498 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term19 _24440 P.
Proof. exact (EQ_MP (@lem1072497 _24440 P) (@lem1072484 _24440 x P h1)). Qed.
Lemma lem1072500 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term17 _24440 P x) = (term17 _24440 P x).
Proof. exact (eq_refl (term17 _24440 P x)). Qed.
Lemma lem1072501 {_24440 : Type'} (P : _24440 -> Prop) : (term18 _24440 P) = (term18 _24440 P).
Proof. exact (fun_ext (fun x : _24440 => @lem1072500 _24440 P x)). Qed.
Lemma lem1072502 {_24440 : Type'} : (@all _24440) = (@all _24440).
Proof. exact (eq_refl (@all _24440)). Qed.
Lemma lem1072504 {_24440 : Type'} (P : _24440 -> Prop) : (term19 _24440 P) = (term19 _24440 P).
Proof. exact (MK_COMB (@lem1072502 _24440) (@lem1072501 _24440 P)). Qed.
Lemma lem1072505 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term19 _24440 P.
Proof. exact (EQ_MP (@lem1072504 _24440 P) (@lem1072487 _24440 P x h1)). Qed.
Lemma lem1072510 {_24440 : Type'} (_17528 : _24440) (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term32 _24440 P _17528.
Proof. exact (@lem1072498 _24440 x P h1 _17528). Qed.
Lemma lem1072511 {_24440 : Type'} (P : _24440 -> Prop) (_17528 : _24440) : (term32 _24440 P _17528) = (term17 _24440 P _17528).
Proof. exact (eq_refl (term32 _24440 P _17528)). Qed.
Lemma lem1072513 {_24440 : Type'} (_17529 : _24440) (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term32 _24440 P _17529.
Proof. exact (@lem1072505 _24440 P x h1 _17529). Qed.
Lemma lem1072514 {_24440 : Type'} (P : _24440 -> Prop) (_17529 : _24440) : (term32 _24440 P _17529) = (term17 _24440 P _17529).
Proof. exact (eq_refl (term32 _24440 P _17529)). Qed.
Lemma lem1072519 {_24440 : Type'} (_17528 : _24440) (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term17 _24440 P _17528.
Proof. exact (EQ_MP (@lem1072511 _24440 P _17528) (@lem1072510 _24440 _17528 x P h1)). Qed.
Lemma lem1072521 {_24440 : Type'} (_17529 : _24440) (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term17 _24440 P _17529.
Proof. exact (EQ_MP (@lem1072514 _24440 P _17529) (@lem1072513 _24440 _17529 P x h1)). Qed.
Lemma lem1072525 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : P x.
Proof. exact (proj1 (@lem1072482 _24440 x P h1)). Qed.
Lemma lem1072526 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term80 _24440 P x.
Proof. exact (fun h0 : term17 _24440 P x => @lem1072525 _24440 x P h1). Qed.
Lemma lem1072528 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1072529 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term80 _24440 P x) = (P x).
Proof. exact (@lem1072528 (P x)). Qed.
Lemma lem1072530 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : P x.
Proof. exact (EQ_MP (@lem1072529 _24440 P x) (@lem1072526 _24440 x P h1)). Qed.
Lemma lem1072533 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1072535 {_24440 : Type'} (P : _24440 -> Prop) (_17528 : _24440) : (term17 _24440 P _17528) = (term82 _24440 P _17528).
Proof. exact (@lem1072533 (P _17528)). Qed.
Lemma lem1072538 {_24440 : Type'} (_17528 : _24440) (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term82 _24440 P _17528.
Proof. exact (EQ_MP (@lem1072535 _24440 P _17528) (@lem1072519 _24440 _17528 x P h1)). Qed.
Lemma lem1072539 {_24440 : Type'} (_17528 : _24440) (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term82 _24440 P _17528.
Proof. exact (@lem1072538 _24440 _17528 x P h1). Qed.
Lemma lem1072540 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term82 _24440 P x.
Proof. exact (@lem1072539 _24440 x x P h1). Qed.
Lemma lem1072543 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : False.
Proof. exact (@lem1072540 _24440 x P h1 (@lem1072530 _24440 x P h1)). Qed.
Lemma lem1072544 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : term83.
Proof. exact (fun h0 : ~ False => @lem1072543 _24440 x P h1). Qed.
Lemma lem1072546 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1072547 : term83 = False.
Proof. exact (@lem1072546 False). Qed.
Lemma lem1072548 {_24440 : Type'} (x : _24440) (P : _24440 -> Prop) (h1 : term62 _24440 x P) : False.
Proof. exact (EQ_MP (@lem1072547) (@lem1072544 _24440 x P h1)). Qed.
Lemma lem1072550 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : P x.
Proof. exact (proj2 (@lem1072483 _24440 P x h1)). Qed.
Lemma lem1072551 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term80 _24440 P x.
Proof. exact (fun h0 : term17 _24440 P x => @lem1072550 _24440 P x h1). Qed.
Lemma lem1072553 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1072554 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) : (term80 _24440 P x) = (P x).
Proof. exact (@lem1072553 (P x)). Qed.
Lemma lem1072555 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : P x.
Proof. exact (EQ_MP (@lem1072554 _24440 P x) (@lem1072551 _24440 P x h1)). Qed.
Lemma lem1072558 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1072560 {_24440 : Type'} (P : _24440 -> Prop) (_17529 : _24440) : (term17 _24440 P _17529) = (term82 _24440 P _17529).
Proof. exact (@lem1072558 (P _17529)). Qed.
Lemma lem1072563 {_24440 : Type'} (_17529 : _24440) (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term82 _24440 P _17529.
Proof. exact (EQ_MP (@lem1072560 _24440 P _17529) (@lem1072521 _24440 _17529 P x h1)). Qed.
Lemma lem1072564 {_24440 : Type'} (_17529 : _24440) (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term82 _24440 P _17529.
Proof. exact (@lem1072563 _24440 _17529 P x h1). Qed.
Lemma lem1072565 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term82 _24440 P x.
Proof. exact (@lem1072564 _24440 x P x h1). Qed.
Lemma lem1072568 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : False.
Proof. exact (@lem1072565 _24440 P x h1 (@lem1072555 _24440 P x h1)). Qed.
Lemma lem1072569 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : term83.
Proof. exact (fun h0 : ~ False => @lem1072568 _24440 P x h1). Qed.
Lemma lem1072571 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1072572 : term83 = False.
Proof. exact (@lem1072571 False). Qed.
Lemma lem1072573 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term67 _24440 P x) : False.
Proof. exact (EQ_MP (@lem1072572) (@lem1072569 _24440 P x h1)). Qed.
Lemma lem1072574 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term75 _24440 P x) : False.
Proof. exact (or_elim (@lem1072481 _24440 P x h1) (fun h0 : term62 _24440 x P => @lem1072548 _24440 x P h0) (fun h0 : term67 _24440 P x => @lem1072573 _24440 P x h0)). Qed.
Lemma lem1072575 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term75 _24440 P x) : (term75 _24440 P x) = False.
Proof. exact (prop_ext (fun h2 : term75 _24440 P x => @lem1072574 _24440 P x h1) (fun h2 : False => @lem1072481 _24440 P x h1)). Qed.
Lemma lem1072576 {_24440 : Type'} (P : _24440 -> Prop) (x : _24440) (h1 : term75 _24440 P x) : False.
Proof. exact (EQ_MP (@lem1072575 _24440 P x h1) (@lem1072481 _24440 P x h1)). Qed.
Lemma lem1072577 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term7 _24440 P) : False.
Proof. exact (ex_elim (@lem1072448 _24440 P h1) (fun x : _24440 => fun h0 : term77 _24440 P x => @lem1072576 _24440 P x h0)). Qed.
Lemma lem1072578 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term7 _24440 P) : (term7 _24440 P) = False.
Proof. exact (prop_ext (fun h2 : term7 _24440 P => @lem1072577 _24440 P h1) (fun h2 : False => @lem1072344 _24440 P h1)). Qed.
Lemma lem1072579 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term7 _24440 P) : False.
Proof. exact (EQ_MP (@lem1072578 _24440 P h1) (@lem1072344 _24440 P h1)). Qed.
Lemma lem1072580 {_24440 : Type'} (P : _24440 -> Prop) : term6 _24440 P.
Proof. exact (fun h0 : term7 _24440 P => @lem1072579 _24440 P h0). Qed.
Lemma lem1072581 {_24440 : Type'} (P : _24440 -> Prop) : (term4 _24440 P) = (term5 _24440 P).
Proof. exact (EQ_MP (@lem1072343 _24440 P) (@lem1072580 _24440 P)). Qed.
Lemma lem1072586 {_24440 : Type'} : term16 _24440.
Proof. exact (fun P : _24440 -> Prop => @lem1072581 _24440 P). Qed.
Lemma lem1072587 {_24440 : Type'} : term15 _24440.
Proof. exact (EQ_MP (@lem1072339 _24440) (@lem1072586 _24440)). Qed.
Lemma lem1072588 {_24440 : Type'} (P : _24440 -> Prop) : term84 _24440 P.
Proof. exact (@lem1072587 _24440 P). Qed.
Lemma lem1072589 {_24440 : Type'} (P : _24440 -> Prop) : (term84 _24440 P) = (term6 _24440 P).
Proof. exact (eq_refl (term84 _24440 P)). Qed.
Lemma lem1072590 {_24440 : Type'} (P : _24440 -> Prop) : term6 _24440 P.
Proof. exact (EQ_MP (@lem1072589 _24440 P) (@lem1072588 _24440 P)). Qed.
Lemma lem1072592 {_24440 : Type'} (P : _24440 -> Prop) : term6 _24440 P.
Proof. exact (@lem1072269 _24440 P (@lem1072590 _24440 P)). Qed.
Lemma lem1072593 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term7 _24440 P) : False.
Proof. exact (@lem1072592 _24440 P (@lem1072253 _24440 P h1)). Qed.
Lemma lem1072594 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term7 _24440 P) : (term7 _24440 P) = False.
Proof. exact (prop_ext (fun h2 : term7 _24440 P => @lem1072593 _24440 P h1) (fun h2 : False => @lem1072253 _24440 P h1)). Qed.
Lemma lem1072595 {_24440 : Type'} (P : _24440 -> Prop) (h1 : term7 _24440 P) : False.
Proof. exact (EQ_MP (@lem1072594 _24440 P h1) (@lem1072253 _24440 P h1)). Qed.
Lemma lem1072596 {_24440 : Type'} (P : _24440 -> Prop) : term6 _24440 P.
Proof. exact (fun h0 : term7 _24440 P => @lem1072595 _24440 P h0). Qed.
Lemma lem1072605 {_24440 : Type'} (P : _24440 -> Prop) : (term4 _24440 P) = (term5 _24440 P).
Proof. exact (EQ_MP (@lem1072252 _24440 P) (@lem1072596 _24440 P)). Qed.
Lemma lem1072606 {A : Type'} (P : type1160 A) : (term85 A P) = (term86 A P).
Proof. exact (@lem1072605 (option A) P). Qed.
Lemma lem1072611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072612 {A : Type'} (P : type1160 A) : (term87 A P) = (term88 A P).
Proof. exact (MK_COMB (@lem1072611) (@lem1072606 A P)). Qed.
Lemma lem1072620 {_24440 : Type'} (P : _24440 -> Prop) : (term4 _24440 P) = (term5 _24440 P).
Proof. exact (EQ_MP (@lem1072252 _24440 P) (@lem1072596 _24440 P)). Qed.
Lemma lem1072621 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (@lem1072620 A P). Qed.
Lemma lem1072622 {A : Type'} (P : type1160 A) : (term89 A P) = (term90 A P).
Proof. exact (@lem1072621 A (term91 A P)). Qed.
Lemma lem1072623 {A : Type'} (P : type1160 A) (a : A) : (term92 A P a) = (term93 A P a).
Proof. exact (eq_refl (term92 A P a)). Qed.
Lemma lem1072624 {A : Type'} (P : type1160 A) : (term94 A P) = (term91 A P).
Proof. exact (fun_ext (fun a : A => @lem1072623 A P a)). Qed.
Lemma lem1072625 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072626 {A : Type'} (P : type1160 A) : (term89 A P) = (term95 A P).
Proof. exact (MK_COMB (@lem1072625 A) (@lem1072624 A P)). Qed.
Lemma lem1072627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072628 {A : Type'} (P : type1160 A) : (term96 A P) = (term97 A P).
Proof. exact (MK_COMB (@lem1072627) (@lem1072626 A P)). Qed.
Lemma lem1072629 {A : Type'} (P : type1160 A) (a : A) : (term92 A P a) = (term93 A P a).
Proof. exact (eq_refl (term92 A P a)). Qed.
Lemma lem1072630 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072631 {A : Type'} (P : type1160 A) (a : A) : (term98 A P a) = (term99 A P a).
Proof. exact (MK_COMB (@lem1072630) (@lem1072629 A P a)). Qed.
Lemma lem1072632 {A : Type'} (P : type1160 A) : (term100 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1072631 A P a)). Qed.
Lemma lem1072633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1072634 {A : Type'} (P : type1160 A) : (term102 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1072633 A) (@lem1072632 A P)). Qed.
Lemma lem1072635 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072636 {A : Type'} (P : type1160 A) : (term90 A P) = (term104 A P).
Proof. exact (MK_COMB (@lem1072635) (@lem1072634 A P)). Qed.
Lemma lem1072637 {A : Type'} (P : type1160 A) : ((term89 A P) = (term90 A P)) = ((term95 A P) = (term104 A P)).
Proof. exact (MK_COMB (@lem1072628 A P) (@lem1072636 A P)). Qed.
Lemma lem1072638 {A : Type'} (P : type1160 A) : (term95 A P) = (term104 A P).
Proof. exact (EQ_MP (@lem1072637 A P) (@lem1072622 A P)). Qed.
Lemma lem1072643 {A : Type'} (P : type1160 A) : (term105 A P) = (term105 A P).
Proof. exact (eq_refl (term105 A P)). Qed.
Lemma lem1072644 {A : Type'} (P : type1160 A) : (term106 A P) = (term107 A P).
Proof. exact (MK_COMB (@lem1072643 A P) (@lem1072638 A P)). Qed.
Lemma lem1072647 {A : Type'} (P : type1160 A) : ((term85 A P) = (term106 A P)) = ((term86 A P) = (term107 A P)).
Proof. exact (MK_COMB (@lem1072612 A P) (@lem1072644 A P)). Qed.
Lemma lem1072650 {A : Type'} (P : type1160 A) : ((term86 A P) = (term107 A P)) = ((term85 A P) = (term106 A P)).
Proof. exact (SYM (@lem1072647 A P)). Qed.
Lemma lem1072658 {_24424 : Type'} (P : type1160 _24424) : (term1 _24424 P) = (term2 _24424 P).
Proof. exact (EQ_MP (@lem1072237 _24424 P) (@lem1072236 _24424 P)). Qed.
Lemma lem1072659 {A : Type'} (P : type1160 A) : (term1 A P) = (term2 A P).
Proof. exact (@lem1072658 A P). Qed.
Lemma lem1072660 {A : Type'} (P : type1160 A) : (term108 A P) = (term109 A P).
Proof. exact (@lem1072659 A (term110 A P)). Qed.
Lemma lem1072661 {A : Type'} (P : type1160 A) (x : option A) : (term111 A P x) = (term112 A P x).
Proof. exact (eq_refl (term111 A P x)). Qed.
Lemma lem1072662 {A : Type'} (P : type1160 A) : (term113 A P) = (term110 A P).
Proof. exact (fun_ext (fun x : option A => @lem1072661 A P x)). Qed.
Lemma lem1072663 {A : Type'} : (@all (option A)) = (@all (option A)).
Proof. exact (eq_refl (@all (option A))). Qed.
Lemma lem1072664 {A : Type'} (P : type1160 A) : (term108 A P) = (term114 A P).
Proof. exact (MK_COMB (@lem1072663 A) (@lem1072662 A P)). Qed.
Lemma lem1072665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072666 {A : Type'} (P : type1160 A) : (term115 A P) = (term116 A P).
Proof. exact (MK_COMB (@lem1072665) (@lem1072664 A P)). Qed.
Lemma lem1072667 {A : Type'} (P : type1160 A) : (term117 A P) = (term118 A P).
Proof. exact (eq_refl (term117 A P)). Qed.
Lemma lem1072668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072669 {A : Type'} (P : type1160 A) : (term119 A P) = (term120 A P).
Proof. exact (MK_COMB (@lem1072668) (@lem1072667 A P)). Qed.
Lemma lem1072670 {A : Type'} (P : type1160 A) (a : A) : (term121 A P a) = (term99 A P a).
Proof. exact (eq_refl (term121 A P a)). Qed.
Lemma lem1072671 {A : Type'} (P : type1160 A) : (term122 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1072670 A P a)). Qed.
Lemma lem1072672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1072673 {A : Type'} (P : type1160 A) : (term123 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1072672 A) (@lem1072671 A P)). Qed.
Lemma lem1072674 {A : Type'} (P : type1160 A) : (term109 A P) = (term124 A P).
Proof. exact (MK_COMB (@lem1072669 A P) (@lem1072673 A P)). Qed.
Lemma lem1072675 {A : Type'} (P : type1160 A) : ((term108 A P) = (term109 A P)) = ((term114 A P) = (term124 A P)).
Proof. exact (MK_COMB (@lem1072666 A P) (@lem1072674 A P)). Qed.
Lemma lem1072676 {A : Type'} (P : type1160 A) : (term114 A P) = (term124 A P).
Proof. exact (EQ_MP (@lem1072675 A P) (@lem1072660 A P)). Qed.
Lemma lem1072685 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072686 {A : Type'} (P : type1160 A) : (term86 A P) = (term125 A P).
Proof. exact (MK_COMB (@lem1072685) (@lem1072676 A P)). Qed.
Lemma lem1072687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072688 {A : Type'} (P : type1160 A) : (term88 A P) = (term126 A P).
Proof. exact (MK_COMB (@lem1072687) (@lem1072686 A P)). Qed.
Lemma lem1072697 {A : Type'} (P : type1160 A) : (term107 A P) = (term107 A P).
Proof. exact (eq_refl (term107 A P)). Qed.
Lemma lem1072698 {A : Type'} (P : type1160 A) : ((term86 A P) = (term107 A P)) = ((term125 A P) = (term107 A P)).
Proof. exact (MK_COMB (@lem1072688 A P) (@lem1072697 A P)). Qed.
Lemma lem1072701 {A : Type'} (P : type1160 A) : ((term125 A P) = (term107 A P)) = ((term86 A P) = (term107 A P)).
Proof. exact (SYM (@lem1072698 A P)). Qed.
Lemma lem1072703 (p : Prop) : p = (term3 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1072704 {A : Type'} (P : type1160 A) : ((term125 A P) = (term107 A P)) = (term127 A P).
Proof. exact (@lem1072703 ((term125 A P) = (term107 A P))). Qed.
Lemma lem1072705 {A : Type'} (P : type1160 A) : (term127 A P) = ((term125 A P) = (term107 A P)).
Proof. exact (SYM (@lem1072704 A P)). Qed.
Lemma lem1072706 {A : Type'} (P : type1160 A) (h1 : term128 A P) : term128 A P.
Proof. exact (h1). Qed.
Lemma lem1072709 {A : Type'} (P : type1160 A) (h1 : term127 A P) : term127 A P.
Proof. exact (h1). Qed.
Lemma lem1072710 {A : Type'} (P : type1160 A) : term129 A P.
Proof. exact (fun h0 : term127 A P => @lem1072709 A P h0). Qed.
Lemma lem1072711 {A : Type'} (P : type1160 A) (h1 : term129 A P) : term129 A P.
Proof. exact (h1). Qed.
Lemma lem1072712 {A : Type'} (P : type1160 A) (h1 : term127 A P) : term127 A P.
Proof. exact (h1). Qed.
Lemma lem1072713 {A : Type'} (P : type1160 A) (h1 : term127 A P) (h2 : term129 A P) : term127 A P.
Proof. exact (@lem1072711 A P h2 (@lem1072712 A P h1)). Qed.
Lemma lem1072714 {A : Type'} (P : type1160 A) (h1 : term127 A P) : term130 A P.
Proof. exact (fun h0 : term129 A P => @lem1072713 A P h1 h0). Qed.
Lemma lem1072715 {A : Type'} (P : type1160 A) (h1 : term129 A P) : term129 A P.
Proof. exact (h1). Qed.
Lemma lem1072716 {A : Type'} (P : type1160 A) (h1 : term127 A P) (h2 : term129 A P) : term127 A P.
Proof. exact (@lem1072714 A P h1 (@lem1072715 A P h2)). Qed.
Lemma lem1072717 {A : Type'} (P : type1160 A) (h1 : term129 A P) : term129 A P.
Proof. exact (fun h0 : term127 A P => @lem1072716 A P h0 h1). Qed.
Lemma lem1072718 {A : Type'} (P : type1160 A) : term131 A P.
Proof. exact (fun h0 : term129 A P => @lem1072717 A P h0). Qed.
Lemma lem1072721 {A : Type'} (P : type1160 A) : term129 A P.
Proof. exact (@lem1072718 A P (@lem1072710 A P)). Qed.
Lemma lem1072722 {A : Type'} (P : type1160 A) : term129 A P.
Proof. exact (@lem1072721 A P). Qed.
Lemma lem1072728 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1072729 {A : Type'} (P : type1160 A) : (term127 A P) = (term132 A P).
Proof. exact (@lem1072728 (term128 A P)). Qed.
Lemma lem1072731 (t : Prop) : (term12 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1072732 {A : Type'} (P : type1160 A) : (term132 A P) = ((term125 A P) = (term107 A P)).
Proof. exact (@lem1072731 ((term125 A P) = (term107 A P))). Qed.
Lemma lem1072733 {A : Type'} (P : type1160 A) : (term127 A P) = ((term125 A P) = (term107 A P)).
Proof. exact (TRANS (@lem1072729 A P) (@lem1072732 A P)). Qed.
Lemma lem1072746 {A : Type'} : (term133 A) = (term134 A).
Proof. exact (fun_ext (fun P : type1160 A => @lem1072733 A P)). Qed.
Lemma lem1072747 {A : Type'} : (@all ((option A) -> Prop)) = (@all ((option A) -> Prop)).
Proof. exact (eq_refl (@all ((option A) -> Prop))). Qed.
Lemma lem1072756 {A : Type'} : (term135 A) = (term136 A).
Proof. exact (MK_COMB (@lem1072747 A) (@lem1072746 A)). Qed.
Lemma lem1072759 {A : Type'} (P : type1160 A) (a : A) : (term99 A P a) = (term99 A P a).
Proof. exact (eq_refl (term99 A P a)). Qed.
Lemma lem1072760 {A : Type'} (P : type1160 A) : (term101 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1072759 A P a)). Qed.
Lemma lem1072761 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1072762 {A : Type'} (P : type1160 A) : (term103 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1072761 A) (@lem1072760 A P)). Qed.
Lemma lem1072763 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072764 {A : Type'} (P : type1160 A) : (term104 A P) = (term104 A P).
Proof. exact (MK_COMB (@lem1072763) (@lem1072762 A P)). Qed.
Lemma lem1072767 {A : Type'} (P : type1160 A) : (term105 A P) = (term105 A P).
Proof. exact (eq_refl (term105 A P)). Qed.
Lemma lem1072768 {A : Type'} (P : type1160 A) : (term107 A P) = (term107 A P).
Proof. exact (MK_COMB (@lem1072767 A P) (@lem1072764 A P)). Qed.
Lemma lem1072771 {A : Type'} (P : type1160 A) (a : A) : (term99 A P a) = (term99 A P a).
Proof. exact (eq_refl (term99 A P a)). Qed.
Lemma lem1072772 {A : Type'} (P : type1160 A) : (term101 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1072771 A P a)). Qed.
Lemma lem1072773 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1072774 {A : Type'} (P : type1160 A) : (term103 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1072773 A) (@lem1072772 A P)). Qed.
Lemma lem1072779 {A : Type'} (P : type1160 A) : (term120 A P) = (term120 A P).
Proof. exact (eq_refl (term120 A P)). Qed.
Lemma lem1072780 {A : Type'} (P : type1160 A) : (term124 A P) = (term124 A P).
Proof. exact (MK_COMB (@lem1072779 A P) (@lem1072774 A P)). Qed.
Lemma lem1072781 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072782 {A : Type'} (P : type1160 A) : (term125 A P) = (term125 A P).
Proof. exact (MK_COMB (@lem1072781) (@lem1072780 A P)). Qed.
Lemma lem1072783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072784 {A : Type'} (P : type1160 A) : (term126 A P) = (term126 A P).
Proof. exact (MK_COMB (@lem1072783) (@lem1072782 A P)). Qed.
Lemma lem1072785 {A : Type'} (P : type1160 A) : ((term125 A P) = (term107 A P)) = ((term125 A P) = (term107 A P)).
Proof. exact (MK_COMB (@lem1072784 A P) (@lem1072768 A P)). Qed.
Lemma lem1072786 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (fun_ext (fun P : type1160 A => @lem1072785 A P)). Qed.
Lemma lem1072787 {A : Type'} : (@all ((option A) -> Prop)) = (@all ((option A) -> Prop)).
Proof. exact (eq_refl (@all ((option A) -> Prop))). Qed.
Lemma lem1072788 {A : Type'} : (term136 A) = (term136 A).
Proof. exact (MK_COMB (@lem1072787 A) (@lem1072786 A)). Qed.
Lemma lem1072813 {A : Type'} : (term135 A) = (term136 A).
Proof. exact (TRANS (@lem1072756 A) (@lem1072788 A)). Qed.
Lemma lem1072814 {A : Type'} : (term136 A) = (term135 A).
Proof. exact (SYM (@lem1072813 A)). Qed.
Lemma lem1072816 (p : Prop) : p = (term3 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1072817 {A : Type'} (P : type1160 A) : ((term125 A P) = (term107 A P)) = (term127 A P).
Proof. exact (@lem1072816 ((term125 A P) = (term107 A P))). Qed.
Lemma lem1072818 {A : Type'} (P : type1160 A) : (term127 A P) = ((term125 A P) = (term107 A P)).
Proof. exact (SYM (@lem1072817 A P)). Qed.
Lemma lem1072819 {A : Type'} (P : type1160 A) (h1 : term128 A P) : term128 A P.
Proof. exact (h1). Qed.
Lemma lem1072823 {A : Type'} (P : type1160 A) : (term137 A P) = (P (@None A)).
Proof. exact (@lem16933 (P (@None A))). Qed.
Lemma lem1072824 {A : Type'} (P : type1160 A) (a : A) : (term99 A P a) = (term99 A P a).
Proof. exact (eq_refl (term99 A P a)). Qed.
Lemma lem1072827 {A : Type'} (P : type1160 A) (a : A) : (term138 A P a) = (term93 A P a).
Proof. exact (@lem16933 (term93 A P a)). Qed.
Lemma lem1072828 {A : Type'} (P : A -> Prop) : (term29 A P) = (term30 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1072829 {A : Type'} (P : type1160 A) : (term104 A P) = (term139 A P).
Proof. exact (@lem1072828 A (term101 A P)). Qed.
Lemma lem1072830 {A : Type'} (P : type1160 A) (a : A) : (term140 A P a) = (term99 A P a).
Proof. exact (eq_refl (term140 A P a)). Qed.
Lemma lem1072831 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072832 {A : Type'} (P : type1160 A) (a : A) : (term141 A P a) = (term138 A P a).
Proof. exact (MK_COMB (@lem1072831) (@lem1072830 A P a)). Qed.
Lemma lem1072833 {A : Type'} (P : type1160 A) (a : A) : (term141 A P a) = (term93 A P a).
Proof. exact (TRANS (@lem1072832 A P a) (@lem1072827 A P a)). Qed.
Lemma lem1072834 {A : Type'} (P : type1160 A) : (term142 A P) = (term91 A P).
Proof. exact (fun_ext (fun a : A => @lem1072833 A P a)). Qed.
Lemma lem1072835 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072836 {A : Type'} (P : type1160 A) : (term139 A P) = (term95 A P).
Proof. exact (MK_COMB (@lem1072835 A) (@lem1072834 A P)). Qed.
Lemma lem1072837 {A : Type'} (P : type1160 A) : (term104 A P) = (term95 A P).
Proof. exact (TRANS (@lem1072829 A P) (@lem1072836 A P)). Qed.
Lemma lem1072838 {A : Type'} (P : type1160 A) : (term101 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1072824 A P a)). Qed.
Lemma lem1072839 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1072840 {A : Type'} (P : type1160 A) : (term103 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1072839 A) (@lem1072838 A P)). Qed.
Lemma lem1072841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1072842 {A : Type'} (P : type1160 A) : (term143 A P) = (term105 A P).
Proof. exact (MK_COMB (@lem1072841) (@lem1072823 A P)). Qed.
Lemma lem1072843 {A : Type'} (P : type1160 A) : (term144 A P) = (term106 A P).
Proof. exact (MK_COMB (@lem1072842 A P) (@lem1072837 A P)). Qed.
Lemma lem1072844 {A : Type'} (P : type1160 A) : (term125 A P) = (term144 A P).
Proof. exact (@lem17045 (term118 A P) (term103 A P)). Qed.
Lemma lem1072845 {A : Type'} (P : type1160 A) : (term125 A P) = (term106 A P).
Proof. exact (TRANS (@lem1072844 A P) (@lem1072843 A P)). Qed.
Lemma lem1072847 {A : Type'} (P : type1160 A) : (term120 A P) = (term120 A P).
Proof. exact (eq_refl (term120 A P)). Qed.
Lemma lem1072848 {A : Type'} (P : type1160 A) : (term124 A P) = (term124 A P).
Proof. exact (MK_COMB (@lem1072847 A P) (@lem1072840 A P)). Qed.
Lemma lem1072849 {A : Type'} (P : type1160 A) : (term145 A P) = (term124 A P).
Proof. exact (@lem16933 (term124 A P)). Qed.
Lemma lem1072850 {A : Type'} (P : type1160 A) : (term145 A P) = (term124 A P).
Proof. exact (TRANS (@lem1072849 A P) (@lem1072848 A P)). Qed.
Lemma lem1072853 {A : Type'} (P : type1160 A) (a : A) : (term99 A P a) = (term99 A P a).
Proof. exact (eq_refl (term99 A P a)). Qed.
Lemma lem1072856 {A : Type'} (P : type1160 A) (a : A) : (term138 A P a) = (term93 A P a).
Proof. exact (@lem16933 (term93 A P a)). Qed.
Lemma lem1072857 {A : Type'} (P : A -> Prop) : (term29 A P) = (term30 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1072858 {A : Type'} (P : type1160 A) : (term104 A P) = (term139 A P).
Proof. exact (@lem1072857 A (term101 A P)). Qed.
Lemma lem1072859 {A : Type'} (P : type1160 A) (a : A) : (term140 A P a) = (term99 A P a).
Proof. exact (eq_refl (term140 A P a)). Qed.
Lemma lem1072860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1072861 {A : Type'} (P : type1160 A) (a : A) : (term141 A P a) = (term138 A P a).
Proof. exact (MK_COMB (@lem1072860) (@lem1072859 A P a)). Qed.
Lemma lem1072862 {A : Type'} (P : type1160 A) (a : A) : (term141 A P a) = (term93 A P a).
Proof. exact (TRANS (@lem1072861 A P a) (@lem1072856 A P a)). Qed.
Lemma lem1072863 {A : Type'} (P : type1160 A) : (term142 A P) = (term91 A P).
Proof. exact (fun_ext (fun a : A => @lem1072862 A P a)). Qed.
Lemma lem1072864 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072865 {A : Type'} (P : type1160 A) : (term139 A P) = (term95 A P).
Proof. exact (MK_COMB (@lem1072864 A) (@lem1072863 A P)). Qed.
Lemma lem1072866 {A : Type'} (P : type1160 A) : (term104 A P) = (term95 A P).
Proof. exact (TRANS (@lem1072858 A P) (@lem1072865 A P)). Qed.
Lemma lem1072867 {A : Type'} (P : type1160 A) : (term101 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1072853 A P a)). Qed.
Lemma lem1072868 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1072869 {A : Type'} (P : type1160 A) : (term103 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1072868 A) (@lem1072867 A P)). Qed.
Lemma lem1072870 {A : Type'} (P : type1160 A) : (term146 A P) = (term103 A P).
Proof. exact (@lem16933 (term103 A P)). Qed.
Lemma lem1072871 {A : Type'} (P : type1160 A) : (term146 A P) = (term103 A P).
Proof. exact (TRANS (@lem1072870 A P) (@lem1072869 A P)). Qed.
Lemma lem1072873 {A : Type'} (P : type1160 A) : (term120 A P) = (term120 A P).
Proof. exact (eq_refl (term120 A P)). Qed.
Lemma lem1072874 {A : Type'} (P : type1160 A) : (term147 A P) = (term124 A P).
Proof. exact (MK_COMB (@lem1072873 A P) (@lem1072871 A P)). Qed.
Lemma lem1072875 {A : Type'} (P : type1160 A) : (term148 A P) = (term147 A P).
Proof. exact (@lem17160 (P (@None A)) (term104 A P)). Qed.
Lemma lem1072876 {A : Type'} (P : type1160 A) : (term148 A P) = (term124 A P).
Proof. exact (TRANS (@lem1072875 A P) (@lem1072874 A P)). Qed.
Lemma lem1072878 {A : Type'} (P : type1160 A) : (term105 A P) = (term105 A P).
Proof. exact (eq_refl (term105 A P)). Qed.
Lemma lem1072879 {A : Type'} (P : type1160 A) : (term107 A P) = (term106 A P).
Proof. exact (MK_COMB (@lem1072878 A P) (@lem1072866 A P)). Qed.
Lemma lem1072880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072881 {A : Type'} (P : type1160 A) : (term149 A P) = (term150 A P).
Proof. exact (MK_COMB (@lem1072880) (@lem1072850 A P)). Qed.
Lemma lem1072882 {A : Type'} (P : type1160 A) : (term151 A P) = (term152 A P).
Proof. exact (MK_COMB (@lem1072881 A P) (@lem1072879 A P)). Qed.
Lemma lem1072883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072884 {A : Type'} (P : type1160 A) : (term153 A P) = (term154 A P).
Proof. exact (MK_COMB (@lem1072883) (@lem1072845 A P)). Qed.
Lemma lem1072885 {A : Type'} (P : type1160 A) : (term155 A P) = (term156 A P).
Proof. exact (MK_COMB (@lem1072884 A P) (@lem1072876 A P)). Qed.
Lemma lem1072886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1072887 {A : Type'} (P : type1160 A) : (term157 A P) = (term158 A P).
Proof. exact (MK_COMB (@lem1072886) (@lem1072885 A P)). Qed.
Lemma lem1072888 {A : Type'} (P : type1160 A) : (term159 A P) = (term160 A P).
Proof. exact (MK_COMB (@lem1072887 A P) (@lem1072882 A P)). Qed.
Lemma lem1072889 {A : Type'} (P : type1160 A) : (term128 A P) = (term159 A P).
Proof. exact (@lem17646 (term125 A P) (term107 A P)). Qed.
Lemma lem1072890 {A : Type'} (P : type1160 A) : (term128 A P) = (term160 A P).
Proof. exact (TRANS (@lem1072889 A P) (@lem1072888 A P)). Qed.
Lemma lem1072909 {A : Type'} (P : Prop) (Q : A -> Prop) : (term161 A P Q) = (term162 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1072910 {A : Type'} (P : Prop) (Q : A -> Prop) : (term161 A P Q) = (term162 A P Q).
Proof. exact (@lem1072909 A P Q). Qed.
Lemma lem1072911 {A : Type'} (P : type1160 A) : (term163 A P) = (term164 A P).
Proof. exact (@lem1072910 A (P (@None A)) (term91 A P)). Qed.
Lemma lem1072912 {A : Type'} (P : type1160 A) (a : A) : (term92 A P a) = (term93 A P a).
Proof. exact (eq_refl (term92 A P a)). Qed.
Lemma lem1072913 {A : Type'} (P : type1160 A) : (term94 A P) = (term91 A P).
Proof. exact (fun_ext (fun a : A => @lem1072912 A P a)). Qed.
Lemma lem1072914 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072915 {A : Type'} (P : type1160 A) : (term89 A P) = (term95 A P).
Proof. exact (MK_COMB (@lem1072914 A) (@lem1072913 A P)). Qed.
Lemma lem1072916 {A : Type'} (P : type1160 A) : (term105 A P) = (term105 A P).
Proof. exact (eq_refl (term105 A P)). Qed.
Lemma lem1072917 {A : Type'} (P : type1160 A) : (term163 A P) = (term106 A P).
Proof. exact (MK_COMB (@lem1072916 A P) (@lem1072915 A P)). Qed.
Lemma lem1072918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072919 {A : Type'} (P : type1160 A) : (term165 A P) = (term166 A P).
Proof. exact (MK_COMB (@lem1072918) (@lem1072917 A P)). Qed.
Lemma lem1072920 {A : Type'} (P : type1160 A) (a : A) : (term92 A P a) = (term93 A P a).
Proof. exact (eq_refl (term92 A P a)). Qed.
Lemma lem1072921 {A : Type'} (P : type1160 A) : (term105 A P) = (term105 A P).
Proof. exact (eq_refl (term105 A P)). Qed.
Lemma lem1072922 {A : Type'} (P : type1160 A) (a : A) : (term167 A P a) = (term168 A P a).
Proof. exact (MK_COMB (@lem1072921 A P) (@lem1072920 A P a)). Qed.
Lemma lem1072923 {A : Type'} (P : type1160 A) : (term169 A P) = (term170 A P).
Proof. exact (fun_ext (fun a : A => @lem1072922 A P a)). Qed.
Lemma lem1072924 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072925 {A : Type'} (P : type1160 A) : (term164 A P) = (term171 A P).
Proof. exact (MK_COMB (@lem1072924 A) (@lem1072923 A P)). Qed.
Lemma lem1072926 {A : Type'} (P : type1160 A) : ((term163 A P) = (term164 A P)) = ((term106 A P) = (term171 A P)).
Proof. exact (MK_COMB (@lem1072919 A P) (@lem1072925 A P)). Qed.
Lemma lem1072927 {A : Type'} (P : type1160 A) : (term106 A P) = (term171 A P).
Proof. exact (EQ_MP (@lem1072926 A P) (@lem1072911 A P)). Qed.
Lemma lem1072928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072929 {A : Type'} (P : type1160 A) : (term154 A P) = (term172 A P).
Proof. exact (MK_COMB (@lem1072928) (@lem1072927 A P)). Qed.
Lemma lem1072930 {A : Type'} (P : type1160 A) : (term124 A P) = (term124 A P).
Proof. exact (eq_refl (term124 A P)). Qed.
Lemma lem1072931 {A : Type'} (P : type1160 A) : (term156 A P) = (term173 A P).
Proof. exact (MK_COMB (@lem1072929 A P) (@lem1072930 A P)). Qed.
Lemma lem1072933 {A : Type'} (P : A -> Prop) (Q : Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1072934 {A : Type'} (P : A -> Prop) (Q : Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (@lem1072933 A P Q). Qed.
Lemma lem1072935 {A : Type'} (P : type1160 A) : (term174 A P) = (term175 A P).
Proof. exact (@lem1072934 A (term170 A P) (term124 A P)). Qed.
Lemma lem1072936 {A : Type'} (P : type1160 A) (a : A) : (term176 A P a) = (term168 A P a).
Proof. exact (eq_refl (term176 A P a)). Qed.
Lemma lem1072937 {A : Type'} (P : type1160 A) : (term177 A P) = (term170 A P).
Proof. exact (fun_ext (fun a : A => @lem1072936 A P a)). Qed.
Lemma lem1072938 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072939 {A : Type'} (P : type1160 A) : (term178 A P) = (term171 A P).
Proof. exact (MK_COMB (@lem1072938 A) (@lem1072937 A P)). Qed.
Lemma lem1072940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072941 {A : Type'} (P : type1160 A) : (term179 A P) = (term172 A P).
Proof. exact (MK_COMB (@lem1072940) (@lem1072939 A P)). Qed.
Lemma lem1072942 {A : Type'} (P : type1160 A) : (term124 A P) = (term124 A P).
Proof. exact (eq_refl (term124 A P)). Qed.
Lemma lem1072943 {A : Type'} (P : type1160 A) : (term174 A P) = (term173 A P).
Proof. exact (MK_COMB (@lem1072941 A P) (@lem1072942 A P)). Qed.
Lemma lem1072944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072945 {A : Type'} (P : type1160 A) : (term180 A P) = (term181 A P).
Proof. exact (MK_COMB (@lem1072944) (@lem1072943 A P)). Qed.
Lemma lem1072946 {A : Type'} (P : type1160 A) (a : A) : (term176 A P a) = (term168 A P a).
Proof. exact (eq_refl (term176 A P a)). Qed.
Lemma lem1072947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072948 {A : Type'} (P : type1160 A) (a : A) : (term182 A P a) = (term183 A P a).
Proof. exact (MK_COMB (@lem1072947) (@lem1072946 A P a)). Qed.
Lemma lem1072949 {A : Type'} (P : type1160 A) : (term124 A P) = (term124 A P).
Proof. exact (eq_refl (term124 A P)). Qed.
Lemma lem1072950 {A : Type'} (a : A) (P : type1160 A) : (term184 A a P) = (term185 A a P).
Proof. exact (MK_COMB (@lem1072948 A P a) (@lem1072949 A P)). Qed.
Lemma lem1072951 {A : Type'} (P : type1160 A) : (term186 A P) = (term187 A P).
Proof. exact (fun_ext (fun a : A => @lem1072950 A a P)). Qed.
Lemma lem1072952 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072953 {A : Type'} (P : type1160 A) : (term175 A P) = (term188 A P).
Proof. exact (MK_COMB (@lem1072952 A) (@lem1072951 A P)). Qed.
Lemma lem1072954 {A : Type'} (P : type1160 A) : ((term174 A P) = (term175 A P)) = ((term173 A P) = (term188 A P)).
Proof. exact (MK_COMB (@lem1072945 A P) (@lem1072953 A P)). Qed.
Lemma lem1072955 {A : Type'} (P : type1160 A) : (term173 A P) = (term188 A P).
Proof. exact (EQ_MP (@lem1072954 A P) (@lem1072935 A P)). Qed.
Lemma lem1072956 {A : Type'} (P : type1160 A) : (term156 A P) = (term188 A P).
Proof. exact (TRANS (@lem1072931 A P) (@lem1072955 A P)). Qed.
Lemma lem1072957 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1072958 {A : Type'} (P : type1160 A) : (term158 A P) = (term189 A P).
Proof. exact (MK_COMB (@lem1072957) (@lem1072956 A P)). Qed.
Lemma lem1072960 {A : Type'} (P : Prop) (Q : A -> Prop) : (term161 A P Q) = (term162 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1072961 {A : Type'} (P : Prop) (Q : A -> Prop) : (term161 A P Q) = (term162 A P Q).
Proof. exact (@lem1072960 A P Q). Qed.
Lemma lem1072962 {A : Type'} (P : type1160 A) : (term163 A P) = (term164 A P).
Proof. exact (@lem1072961 A (P (@None A)) (term91 A P)). Qed.
Lemma lem1072963 {A : Type'} (P : type1160 A) (a : A) : (term92 A P a) = (term93 A P a).
Proof. exact (eq_refl (term92 A P a)). Qed.
Lemma lem1072964 {A : Type'} (P : type1160 A) : (term94 A P) = (term91 A P).
Proof. exact (fun_ext (fun a : A => @lem1072963 A P a)). Qed.
Lemma lem1072965 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072966 {A : Type'} (P : type1160 A) : (term89 A P) = (term95 A P).
Proof. exact (MK_COMB (@lem1072965 A) (@lem1072964 A P)). Qed.
Lemma lem1072967 {A : Type'} (P : type1160 A) : (term105 A P) = (term105 A P).
Proof. exact (eq_refl (term105 A P)). Qed.
Lemma lem1072968 {A : Type'} (P : type1160 A) : (term163 A P) = (term106 A P).
Proof. exact (MK_COMB (@lem1072967 A P) (@lem1072966 A P)). Qed.
Lemma lem1072969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072970 {A : Type'} (P : type1160 A) : (term165 A P) = (term166 A P).
Proof. exact (MK_COMB (@lem1072969) (@lem1072968 A P)). Qed.
Lemma lem1072971 {A : Type'} (P : type1160 A) (a : A) : (term92 A P a) = (term93 A P a).
Proof. exact (eq_refl (term92 A P a)). Qed.
Lemma lem1072972 {A : Type'} (P : type1160 A) : (term105 A P) = (term105 A P).
Proof. exact (eq_refl (term105 A P)). Qed.
Lemma lem1072973 {A : Type'} (P : type1160 A) (a : A) : (term167 A P a) = (term168 A P a).
Proof. exact (MK_COMB (@lem1072972 A P) (@lem1072971 A P a)). Qed.
Lemma lem1072974 {A : Type'} (P : type1160 A) : (term169 A P) = (term170 A P).
Proof. exact (fun_ext (fun a : A => @lem1072973 A P a)). Qed.
Lemma lem1072975 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072976 {A : Type'} (P : type1160 A) : (term164 A P) = (term171 A P).
Proof. exact (MK_COMB (@lem1072975 A) (@lem1072974 A P)). Qed.
Lemma lem1072977 {A : Type'} (P : type1160 A) : ((term163 A P) = (term164 A P)) = ((term106 A P) = (term171 A P)).
Proof. exact (MK_COMB (@lem1072970 A P) (@lem1072976 A P)). Qed.
Lemma lem1072978 {A : Type'} (P : type1160 A) : (term106 A P) = (term171 A P).
Proof. exact (EQ_MP (@lem1072977 A P) (@lem1072962 A P)). Qed.
Lemma lem1072979 {A : Type'} (P : type1160 A) : (term150 A P) = (term150 A P).
Proof. exact (eq_refl (term150 A P)). Qed.
Lemma lem1072980 {A : Type'} (P : type1160 A) : (term152 A P) = (term190 A P).
Proof. exact (MK_COMB (@lem1072979 A P) (@lem1072978 A P)). Qed.
Lemma lem1072982 {A : Type'} (P : Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1072983 {A : Type'} (P : Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (@lem1072982 A P Q). Qed.
Lemma lem1072984 {A : Type'} (P : type1160 A) : (term191 A P) = (term192 A P).
Proof. exact (@lem1072983 A (term124 A P) (term170 A P)). Qed.
Lemma lem1072985 {A : Type'} (P : type1160 A) (a : A) : (term176 A P a) = (term168 A P a).
Proof. exact (eq_refl (term176 A P a)). Qed.
Lemma lem1072986 {A : Type'} (P : type1160 A) : (term177 A P) = (term170 A P).
Proof. exact (fun_ext (fun a : A => @lem1072985 A P a)). Qed.
Lemma lem1072987 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072988 {A : Type'} (P : type1160 A) : (term178 A P) = (term171 A P).
Proof. exact (MK_COMB (@lem1072987 A) (@lem1072986 A P)). Qed.
Lemma lem1072989 {A : Type'} (P : type1160 A) : (term150 A P) = (term150 A P).
Proof. exact (eq_refl (term150 A P)). Qed.
Lemma lem1072990 {A : Type'} (P : type1160 A) : (term191 A P) = (term190 A P).
Proof. exact (MK_COMB (@lem1072989 A P) (@lem1072988 A P)). Qed.
Lemma lem1072991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1072992 {A : Type'} (P : type1160 A) : (term193 A P) = (term194 A P).
Proof. exact (MK_COMB (@lem1072991) (@lem1072990 A P)). Qed.
Lemma lem1072993 {A : Type'} (P : type1160 A) (a : A) : (term176 A P a) = (term168 A P a).
Proof. exact (eq_refl (term176 A P a)). Qed.
Lemma lem1072994 {A : Type'} (P : type1160 A) : (term150 A P) = (term150 A P).
Proof. exact (eq_refl (term150 A P)). Qed.
Lemma lem1072995 {A : Type'} (P : type1160 A) (a : A) : (term195 A P a) = (term196 A P a).
Proof. exact (MK_COMB (@lem1072994 A P) (@lem1072993 A P a)). Qed.
Lemma lem1072996 {A : Type'} (P : type1160 A) : (term197 A P) = (term198 A P).
Proof. exact (fun_ext (fun a : A => @lem1072995 A P a)). Qed.
Lemma lem1072997 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1072998 {A : Type'} (P : type1160 A) : (term192 A P) = (term199 A P).
Proof. exact (MK_COMB (@lem1072997 A) (@lem1072996 A P)). Qed.
Lemma lem1072999 {A : Type'} (P : type1160 A) : ((term191 A P) = (term192 A P)) = ((term190 A P) = (term199 A P)).
Proof. exact (MK_COMB (@lem1072992 A P) (@lem1072998 A P)). Qed.
Lemma lem1073000 {A : Type'} (P : type1160 A) : (term190 A P) = (term199 A P).
Proof. exact (EQ_MP (@lem1072999 A P) (@lem1072984 A P)). Qed.
Lemma lem1073001 {A : Type'} (P : type1160 A) : (term152 A P) = (term199 A P).
Proof. exact (TRANS (@lem1072980 A P) (@lem1073000 A P)). Qed.
Lemma lem1073002 {A : Type'} (P : type1160 A) : (term160 A P) = (term200 A P).
Proof. exact (MK_COMB (@lem1072958 A P) (@lem1073001 A P)). Qed.
Lemma lem1073004 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1073005 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term56 A P Q).
Proof. exact (@lem1073004 A P Q). Qed.
Lemma lem1073006 {A : Type'} (P : type1160 A) : (term201 A P) = (term202 A P).
Proof. exact (@lem1073005 A (term187 A P) (term198 A P)). Qed.
Lemma lem1073007 {A : Type'} (a : A) (P : type1160 A) : (term203 A P a) = (term185 A a P).
Proof. exact (eq_refl (term203 A P a)). Qed.
Lemma lem1073008 {A : Type'} (P : type1160 A) : (term204 A P) = (term187 A P).
Proof. exact (fun_ext (fun a : A => @lem1073007 A a P)). Qed.
Lemma lem1073009 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1073010 {A : Type'} (P : type1160 A) : (term205 A P) = (term188 A P).
Proof. exact (MK_COMB (@lem1073009 A) (@lem1073008 A P)). Qed.
Lemma lem1073011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1073012 {A : Type'} (P : type1160 A) : (term206 A P) = (term189 A P).
Proof. exact (MK_COMB (@lem1073011) (@lem1073010 A P)). Qed.
Lemma lem1073013 {A : Type'} (P : type1160 A) (a : A) : (term207 A P a) = (term196 A P a).
Proof. exact (eq_refl (term207 A P a)). Qed.
Lemma lem1073014 {A : Type'} (P : type1160 A) : (term208 A P) = (term198 A P).
Proof. exact (fun_ext (fun a : A => @lem1073013 A P a)). Qed.
Lemma lem1073015 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1073016 {A : Type'} (P : type1160 A) : (term209 A P) = (term199 A P).
Proof. exact (MK_COMB (@lem1073015 A) (@lem1073014 A P)). Qed.
Lemma lem1073017 {A : Type'} (P : type1160 A) : (term201 A P) = (term200 A P).
Proof. exact (MK_COMB (@lem1073012 A P) (@lem1073016 A P)). Qed.
Lemma lem1073018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1073019 {A : Type'} (P : type1160 A) : (term210 A P) = (term211 A P).
Proof. exact (MK_COMB (@lem1073018) (@lem1073017 A P)). Qed.
Lemma lem1073020 {A : Type'} (a : A) (P : type1160 A) : (term203 A P a) = (term185 A a P).
Proof. exact (eq_refl (term203 A P a)). Qed.
Lemma lem1073021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1073022 {A : Type'} (a : A) (P : type1160 A) : (term212 A P a) = (term213 A a P).
Proof. exact (MK_COMB (@lem1073021) (@lem1073020 A a P)). Qed.
Lemma lem1073023 {A : Type'} (P : type1160 A) (a : A) : (term207 A P a) = (term196 A P a).
Proof. exact (eq_refl (term207 A P a)). Qed.
Lemma lem1073024 {A : Type'} (P : type1160 A) (a : A) : (term214 A P a) = (term215 A P a).
Proof. exact (MK_COMB (@lem1073022 A a P) (@lem1073023 A P a)). Qed.
Lemma lem1073025 {A : Type'} (P : type1160 A) : (term216 A P) = (term217 A P).
Proof. exact (fun_ext (fun a : A => @lem1073024 A P a)). Qed.
Lemma lem1073026 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1073027 {A : Type'} (P : type1160 A) : (term202 A P) = (term218 A P).
Proof. exact (MK_COMB (@lem1073026 A) (@lem1073025 A P)). Qed.
Lemma lem1073028 {A : Type'} (P : type1160 A) : ((term201 A P) = (term202 A P)) = ((term200 A P) = (term218 A P)).
Proof. exact (MK_COMB (@lem1073019 A P) (@lem1073027 A P)). Qed.
Lemma lem1073029 {A : Type'} (P : type1160 A) : (term200 A P) = (term218 A P).
Proof. exact (EQ_MP (@lem1073028 A P) (@lem1073006 A P)). Qed.
Lemma lem1073031 {A : Type'} (P : type1160 A) : (term160 A P) = (term218 A P).
Proof. exact (TRANS (@lem1073002 A P) (@lem1073029 A P)). Qed.
Lemma lem1073032 {A : Type'} (P : type1160 A) : (term128 A P) = (term218 A P).
Proof. exact (TRANS (@lem1072890 A P) (@lem1073031 A P)). Qed.
Lemma lem1073033 {A : Type'} (P : type1160 A) (h1 : term128 A P) : term218 A P.
Proof. exact (EQ_MP (@lem1073032 A P) (@lem1072819 A P h1)). Qed.
Lemma lem1073034 {A : Type'} (P : type1160 A) (a : A) (h1 : term215 A P a) : term215 A P a.
Proof. exact (h1). Qed.
Lemma lem1073045 {A : Type'} (P : type1160 A) (a : A) : (term168 A P a) = (term168 A P a).
Proof. exact (eq_refl (term168 A P a)). Qed.
Lemma lem1073052 {A : Type'} (P : type1160 A) (a : A) : (term99 A P a) = (term99 A P a).
Proof. exact (eq_refl (term99 A P a)). Qed.
Lemma lem1073053 {A : Type'} (P : type1160 A) : (term101 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1073052 A P a)). Qed.
Lemma lem1073054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1073055 {A : Type'} (P : type1160 A) : (term103 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1073054 A) (@lem1073053 A P)). Qed.
Lemma lem1073062 {A : Type'} (P : type1160 A) : (term120 A P) = (term120 A P).
Proof. exact (eq_refl (term120 A P)). Qed.
Lemma lem1073063 {A : Type'} (P : type1160 A) : (term124 A P) = (term124 A P).
Proof. exact (MK_COMB (@lem1073062 A P) (@lem1073055 A P)). Qed.
Lemma lem1073064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1073065 {A : Type'} (P : type1160 A) : (term150 A P) = (term150 A P).
Proof. exact (MK_COMB (@lem1073064) (@lem1073063 A P)). Qed.
Lemma lem1073066 {A : Type'} (P : type1160 A) (a : A) : (term196 A P a) = (term196 A P a).
Proof. exact (MK_COMB (@lem1073065 A P) (@lem1073045 A P a)). Qed.
Lemma lem1073073 {A : Type'} (P : type1160 A) (a : A) : (term99 A P a) = (term99 A P a).
Proof. exact (eq_refl (term99 A P a)). Qed.
Lemma lem1073074 {A : Type'} (P : type1160 A) : (term101 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1073073 A P a)). Qed.
Lemma lem1073075 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1073076 {A : Type'} (P : type1160 A) : (term103 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1073075 A) (@lem1073074 A P)). Qed.
Lemma lem1073083 {A : Type'} (P : type1160 A) : (term120 A P) = (term120 A P).
Proof. exact (eq_refl (term120 A P)). Qed.
Lemma lem1073084 {A : Type'} (P : type1160 A) : (term124 A P) = (term124 A P).
Proof. exact (MK_COMB (@lem1073083 A P) (@lem1073076 A P)). Qed.
Lemma lem1073097 {A : Type'} (P : type1160 A) (a : A) : (term183 A P a) = (term183 A P a).
Proof. exact (eq_refl (term183 A P a)). Qed.
Lemma lem1073098 {A : Type'} (a : A) (P : type1160 A) : (term185 A a P) = (term185 A a P).
Proof. exact (MK_COMB (@lem1073097 A P a) (@lem1073084 A P)). Qed.
Lemma lem1073099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1073100 {A : Type'} (a : A) (P : type1160 A) : (term213 A a P) = (term213 A a P).
Proof. exact (MK_COMB (@lem1073099) (@lem1073098 A a P)). Qed.
Lemma lem1073101 {A : Type'} (P : type1160 A) (a : A) : (term215 A P a) = (term215 A P a).
Proof. exact (MK_COMB (@lem1073100 A a P) (@lem1073066 A P a)). Qed.
Lemma lem1073102 {A : Type'} (P : type1160 A) (a : A) (h1 : term215 A P a) : term215 A P a.
Proof. exact (EQ_MP (@lem1073101 A P a) (@lem1073034 A P a h1)). Qed.
Lemma lem1073103 {A : Type'} (a : A) (P : type1160 A) (h1 : term185 A a P) : term185 A a P.
Proof. exact (h1). Qed.
Lemma lem1073104 {A : Type'} (P : type1160 A) (a : A) (h1 : term196 A P a) : term196 A P a.
Proof. exact (h1). Qed.
Lemma lem1073105 {A : Type'} (a : A) (P : type1160 A) (h1 : term185 A a P) : term124 A P.
Proof. exact (proj2 (@lem1073103 A a P h1)). Qed.
Lemma lem1073106 {A : Type'} (a : A) (P : type1160 A) (h1 : term185 A a P) : term168 A P a.
Proof. exact (proj1 (@lem1073103 A a P h1)). Qed.
Lemma lem1073107 {A : Type'} (a : A) (P : type1160 A) (h1 : term185 A a P) : term103 A P.
Proof. exact (proj2 (@lem1073105 A a P h1)). Qed.
Lemma lem1073111 {A : Type'} (P : type1160 A) (a : A) (h1 : term196 A P a) : term168 A P a.
Proof. exact (proj2 (@lem1073104 A P a h1)). Qed.
Lemma lem1073112 {A : Type'} (P : type1160 A) (a : A) (h1 : term196 A P a) : term124 A P.
Proof. exact (proj1 (@lem1073104 A P a h1)). Qed.
Lemma lem1073113 {A : Type'} (P : type1160 A) (a : A) (h1 : term196 A P a) : term103 A P.
Proof. exact (proj2 (@lem1073112 A P a h1)). Qed.
Lemma lem1073131 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : P (@None A).
Proof. exact (h1). Qed.
Lemma lem1073137 {A : Type'} (P : type1160 A) (a : A) : (term99 A P a) = (term99 A P a).
Proof. exact (eq_refl (term99 A P a)). Qed.
Lemma lem1073138 {A : Type'} (P : type1160 A) : (term101 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1073137 A P a)). Qed.
Lemma lem1073139 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1073141 {A : Type'} (P : type1160 A) : (term103 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1073139 A) (@lem1073138 A P)). Qed.
Lemma lem1073142 {A : Type'} (a : A) (P : type1160 A) (h1 : term185 A a P) : term103 A P.
Proof. exact (EQ_MP (@lem1073141 A P) (@lem1073107 A a P h1)). Qed.
Lemma lem1073146 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term93 A P a.
Proof. exact (h1). Qed.
Lemma lem1073161 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : P (@None A).
Proof. exact (h1). Qed.
Lemma lem1073167 {A : Type'} (P : type1160 A) (a : A) : (term99 A P a) = (term99 A P a).
Proof. exact (eq_refl (term99 A P a)). Qed.
Lemma lem1073168 {A : Type'} (P : type1160 A) : (term101 A P) = (term101 A P).
Proof. exact (fun_ext (fun a : A => @lem1073167 A P a)). Qed.
Lemma lem1073169 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1073171 {A : Type'} (P : type1160 A) : (term103 A P) = (term103 A P).
Proof. exact (MK_COMB (@lem1073169 A) (@lem1073168 A P)). Qed.
Lemma lem1073172 {A : Type'} (P : type1160 A) (a : A) (h1 : term196 A P a) : term103 A P.
Proof. exact (EQ_MP (@lem1073171 A P) (@lem1073113 A P a h1)). Qed.
Lemma lem1073176 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term93 A P a.
Proof. exact (h1). Qed.
Lemma lem1073180 {A : Type'} (_17531 : A) (a : A) (P : type1160 A) (h1 : term185 A a P) : term140 A P _17531.
Proof. exact (@lem1073142 A a P h1 _17531). Qed.
Lemma lem1073181 {A : Type'} (P : type1160 A) (_17531 : A) : (term140 A P _17531) = (term99 A P _17531).
Proof. exact (eq_refl (term140 A P _17531)). Qed.
Lemma lem1073186 {A : Type'} (_17533 : A) (P : type1160 A) (a : A) (h1 : term196 A P a) : term140 A P _17533.
Proof. exact (@lem1073172 A P a h1 _17533). Qed.
Lemma lem1073187 {A : Type'} (P : type1160 A) (_17533 : A) : (term140 A P _17533) = (term99 A P _17533).
Proof. exact (eq_refl (term140 A P _17533)). Qed.
Lemma lem1073190 {A : Type'} (a : A) (P : type1160 A) (h1 : term185 A a P) : term118 A P.
Proof. exact (proj1 (@lem1073105 A a P h1)). Qed.
Lemma lem1073194 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : P (@None A).
Proof. exact (h1). Qed.
Lemma lem1073198 {A : Type'} (_17531 : A) (a : A) (P : type1160 A) (h1 : term185 A a P) : term99 A P _17531.
Proof. exact (EQ_MP (@lem1073181 A P _17531) (@lem1073180 A _17531 a P h1)). Qed.
Lemma lem1073200 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term93 A P a.
Proof. exact (h1). Qed.
Lemma lem1073202 {A : Type'} (P : type1160 A) (a : A) (h1 : term196 A P a) : term118 A P.
Proof. exact (proj1 (@lem1073112 A P a h1)). Qed.
Lemma lem1073206 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : P (@None A).
Proof. exact (h1). Qed.
Lemma lem1073210 {A : Type'} (_17533 : A) (P : type1160 A) (a : A) (h1 : term196 A P a) : term99 A P _17533.
Proof. exact (EQ_MP (@lem1073187 A P _17533) (@lem1073186 A _17533 P a h1)). Qed.
Lemma lem1073212 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term93 A P a.
Proof. exact (h1). Qed.
Lemma lem1073214 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : P (@None A).
Proof. exact (h1). Qed.
Lemma lem1073215 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : term219 A P.
Proof. exact (fun h0 : term118 A P => @lem1073214 A P h1). Qed.
Lemma lem1073217 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1073218 {A : Type'} (P : type1160 A) : (term219 A P) = (P (@None A)).
Proof. exact (@lem1073217 (P (@None A))). Qed.
Lemma lem1073219 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : P (@None A).
Proof. exact (EQ_MP (@lem1073218 A P) (@lem1073215 A P h1)). Qed.
Lemma lem1073222 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1073224 {A : Type'} (P : type1160 A) : (term118 A P) = (term220 A P).
Proof. exact (@lem1073222 (P (@None A))). Qed.
Lemma lem1073227 {A : Type'} (a : A) (P : type1160 A) (h1 : term185 A a P) : term220 A P.
Proof. exact (EQ_MP (@lem1073224 A P) (@lem1073190 A a P h1)). Qed.
Lemma lem1073230 {A : Type'} (a : A) (P : type1160 A) (h1 : P (@None A)) (h2 : term185 A a P) : False.
Proof. exact (@lem1073227 A a P h2 (@lem1073219 A P h1)). Qed.
Lemma lem1073231 {A : Type'} (a : A) (P : type1160 A) (h1 : P (@None A)) (h2 : term185 A a P) : term83.
Proof. exact (fun h0 : ~ False => @lem1073230 A a P h1 h2). Qed.
Lemma lem1073233 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1073234 : term83 = False.
Proof. exact (@lem1073233 False). Qed.
Lemma lem1073235 {A : Type'} (a : A) (P : type1160 A) (h1 : P (@None A)) (h2 : term185 A a P) : False.
Proof. exact (EQ_MP (@lem1073234) (@lem1073231 A a P h1 h2)). Qed.
Lemma lem1073237 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term93 A P a.
Proof. exact (h1). Qed.
Lemma lem1073238 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term221 A P a.
Proof. exact (fun h0 : term99 A P a => @lem1073237 A P a h1). Qed.
Lemma lem1073240 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1073241 {A : Type'} (P : type1160 A) (a : A) : (term221 A P a) = (term93 A P a).
Proof. exact (@lem1073240 (term93 A P a)). Qed.
Lemma lem1073242 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term93 A P a.
Proof. exact (EQ_MP (@lem1073241 A P a) (@lem1073238 A P a h1)). Qed.
Lemma lem1073245 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1073247 {A : Type'} (P : type1160 A) (_17531 : A) : (term99 A P _17531) = (term222 A P _17531).
Proof. exact (@lem1073245 (term93 A P _17531)). Qed.
Lemma lem1073250 {A : Type'} (_17531 : A) (a : A) (P : type1160 A) (h1 : term185 A a P) : term222 A P _17531.
Proof. exact (EQ_MP (@lem1073247 A P _17531) (@lem1073198 A _17531 a P h1)). Qed.
Lemma lem1073251 {A : Type'} (_17531 : A) (a : A) (P : type1160 A) (h1 : term185 A a P) : term222 A P _17531.
Proof. exact (@lem1073250 A _17531 a P h1). Qed.
Lemma lem1073252 {A : Type'} (a : A) (P : type1160 A) (h1 : term185 A a P) : term222 A P a.
Proof. exact (@lem1073251 A a a P h1). Qed.
Lemma lem1073255 {A : Type'} (a : A) (P : type1160 A) (h1 : term93 A P a) (h2 : term185 A a P) : False.
Proof. exact (@lem1073252 A a P h2 (@lem1073242 A P a h1)). Qed.
Lemma lem1073256 {A : Type'} (a : A) (P : type1160 A) (h1 : term93 A P a) (h2 : term185 A a P) : term83.
Proof. exact (fun h0 : ~ False => @lem1073255 A a P h1 h2). Qed.
Lemma lem1073258 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1073259 : term83 = False.
Proof. exact (@lem1073258 False). Qed.
Lemma lem1073260 {A : Type'} (a : A) (P : type1160 A) (h1 : term93 A P a) (h2 : term185 A a P) : False.
Proof. exact (EQ_MP (@lem1073259) (@lem1073256 A a P h1 h2)). Qed.
Lemma lem1073262 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : P (@None A).
Proof. exact (h1). Qed.
Lemma lem1073263 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : term219 A P.
Proof. exact (fun h0 : term118 A P => @lem1073262 A P h1). Qed.
Lemma lem1073265 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1073266 {A : Type'} (P : type1160 A) : (term219 A P) = (P (@None A)).
Proof. exact (@lem1073265 (P (@None A))). Qed.
Lemma lem1073267 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : P (@None A).
Proof. exact (EQ_MP (@lem1073266 A P) (@lem1073263 A P h1)). Qed.
Lemma lem1073270 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1073272 {A : Type'} (P : type1160 A) : (term118 A P) = (term220 A P).
Proof. exact (@lem1073270 (P (@None A))). Qed.
Lemma lem1073275 {A : Type'} (P : type1160 A) (a : A) (h1 : term196 A P a) : term220 A P.
Proof. exact (EQ_MP (@lem1073272 A P) (@lem1073202 A P a h1)). Qed.
Lemma lem1073278 {A : Type'} (P : type1160 A) (a : A) (h1 : P (@None A)) (h2 : term196 A P a) : False.
Proof. exact (@lem1073275 A P a h2 (@lem1073267 A P h1)). Qed.
Lemma lem1073279 {A : Type'} (P : type1160 A) (a : A) (h1 : P (@None A)) (h2 : term196 A P a) : term83.
Proof. exact (fun h0 : ~ False => @lem1073278 A P a h1 h2). Qed.
Lemma lem1073281 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1073282 : term83 = False.
Proof. exact (@lem1073281 False). Qed.
Lemma lem1073283 {A : Type'} (P : type1160 A) (a : A) (h1 : P (@None A)) (h2 : term196 A P a) : False.
Proof. exact (EQ_MP (@lem1073282) (@lem1073279 A P a h1 h2)). Qed.
Lemma lem1073285 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term93 A P a.
Proof. exact (h1). Qed.
Lemma lem1073286 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term221 A P a.
Proof. exact (fun h0 : term99 A P a => @lem1073285 A P a h1). Qed.
Lemma lem1073288 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1073289 {A : Type'} (P : type1160 A) (a : A) : (term221 A P a) = (term93 A P a).
Proof. exact (@lem1073288 (term93 A P a)). Qed.
Lemma lem1073290 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) : term93 A P a.
Proof. exact (EQ_MP (@lem1073289 A P a) (@lem1073286 A P a h1)). Qed.
Lemma lem1073293 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1073295 {A : Type'} (P : type1160 A) (_17533 : A) : (term99 A P _17533) = (term222 A P _17533).
Proof. exact (@lem1073293 (term93 A P _17533)). Qed.
Lemma lem1073298 {A : Type'} (_17533 : A) (P : type1160 A) (a : A) (h1 : term196 A P a) : term222 A P _17533.
Proof. exact (EQ_MP (@lem1073295 A P _17533) (@lem1073210 A _17533 P a h1)). Qed.
Lemma lem1073299 {A : Type'} (_17533 : A) (P : type1160 A) (a : A) (h1 : term196 A P a) : term222 A P _17533.
Proof. exact (@lem1073298 A _17533 P a h1). Qed.
Lemma lem1073300 {A : Type'} (P : type1160 A) (a : A) (h1 : term196 A P a) : term222 A P a.
Proof. exact (@lem1073299 A a P a h1). Qed.
Lemma lem1073303 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) (h2 : term196 A P a) : False.
Proof. exact (@lem1073300 A P a h2 (@lem1073290 A P a h1)). Qed.
Lemma lem1073304 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) (h2 : term196 A P a) : term83.
Proof. exact (fun h0 : ~ False => @lem1073303 A P a h1 h2). Qed.
Lemma lem1073306 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1073307 : term83 = False.
Proof. exact (@lem1073306 False). Qed.
Lemma lem1073308 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) (h2 : term196 A P a) : False.
Proof. exact (EQ_MP (@lem1073307) (@lem1073304 A P a h1 h2)). Qed.
Lemma lem1073309 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) (h2 : term196 A P a) : (term93 A P a) = False.
Proof. exact (prop_ext (fun h3 : term93 A P a => @lem1073308 A P a h1 h2) (fun h3 : False => @lem1073212 A P a h1)). Qed.
Lemma lem1073310 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) (h2 : term196 A P a) : False.
Proof. exact (EQ_MP (@lem1073309 A P a h1 h2) (@lem1073212 A P a h1)). Qed.
Lemma lem1073311 {A : Type'} (P : type1160 A) (a : A) (h1 : P (@None A)) (h2 : term196 A P a) : (P (@None A)) = False.
Proof. exact (prop_ext (fun h3 : P (@None A) => @lem1073283 A P a h1 h2) (fun h3 : False => @lem1073206 A P h1)). Qed.
Lemma lem1073312 {A : Type'} (P : type1160 A) (a : A) (h1 : P (@None A)) (h2 : term196 A P a) : False.
Proof. exact (EQ_MP (@lem1073311 A P a h1 h2) (@lem1073206 A P h1)). Qed.
Lemma lem1073313 {A : Type'} (a : A) (P : type1160 A) (h1 : term93 A P a) (h2 : term185 A a P) : (term93 A P a) = False.
Proof. exact (prop_ext (fun h3 : term93 A P a => @lem1073260 A a P h1 h2) (fun h3 : False => @lem1073200 A P a h1)). Qed.
Lemma lem1073314 {A : Type'} (a : A) (P : type1160 A) (h1 : term93 A P a) (h2 : term185 A a P) : False.
Proof. exact (EQ_MP (@lem1073313 A a P h1 h2) (@lem1073200 A P a h1)). Qed.
Lemma lem1073315 {A : Type'} (a : A) (P : type1160 A) (h1 : P (@None A)) (h2 : term185 A a P) : (P (@None A)) = False.
Proof. exact (prop_ext (fun h3 : P (@None A) => @lem1073235 A a P h1 h2) (fun h3 : False => @lem1073194 A P h1)). Qed.
Lemma lem1073316 {A : Type'} (a : A) (P : type1160 A) (h1 : P (@None A)) (h2 : term185 A a P) : False.
Proof. exact (EQ_MP (@lem1073315 A a P h1 h2) (@lem1073194 A P h1)). Qed.
Lemma lem1073317 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) (h2 : term196 A P a) : (term93 A P a) = False.
Proof. exact (prop_ext (fun h3 : term93 A P a => @lem1073310 A P a h1 h2) (fun h3 : False => @lem1073176 A P a h1)). Qed.
Lemma lem1073318 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) (h2 : term196 A P a) : False.
Proof. exact (EQ_MP (@lem1073317 A P a h1 h2) (@lem1073176 A P a h1)). Qed.
Lemma lem1073319 {A : Type'} (P : type1160 A) (a : A) (h1 : P (@None A)) (h2 : term196 A P a) : (P (@None A)) = False.
Proof. exact (prop_ext (fun h3 : P (@None A) => @lem1073312 A P a h1 h2) (fun h3 : False => @lem1073161 A P h1)). Qed.
Lemma lem1073320 {A : Type'} (P : type1160 A) (a : A) (h1 : P (@None A)) (h2 : term196 A P a) : False.
Proof. exact (EQ_MP (@lem1073319 A P a h1 h2) (@lem1073161 A P h1)). Qed.
Lemma lem1073321 {A : Type'} (a : A) (P : type1160 A) (h1 : term93 A P a) (h2 : term185 A a P) : (term93 A P a) = False.
Proof. exact (prop_ext (fun h3 : term93 A P a => @lem1073314 A a P h1 h2) (fun h3 : False => @lem1073146 A P a h1)). Qed.
Lemma lem1073322 {A : Type'} (a : A) (P : type1160 A) (h1 : term93 A P a) (h2 : term185 A a P) : False.
Proof. exact (EQ_MP (@lem1073321 A a P h1 h2) (@lem1073146 A P a h1)). Qed.
Lemma lem1073323 {A : Type'} (a : A) (P : type1160 A) (h1 : P (@None A)) (h2 : term185 A a P) : (P (@None A)) = False.
Proof. exact (prop_ext (fun h3 : P (@None A) => @lem1073316 A a P h1 h2) (fun h3 : False => @lem1073131 A P h1)). Qed.
Lemma lem1073324 {A : Type'} (a : A) (P : type1160 A) (h1 : P (@None A)) (h2 : term185 A a P) : False.
Proof. exact (EQ_MP (@lem1073323 A a P h1 h2) (@lem1073131 A P h1)). Qed.
Lemma lem1073325 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) (h2 : term196 A P a) : (term93 A P a) = False.
Proof. exact (prop_ext (fun h3 : term93 A P a => @lem1073318 A P a h1 h2) (fun h3 : False => @lem1073176 A P a h1)). Qed.
Lemma lem1073326 {A : Type'} (P : type1160 A) (a : A) (h1 : term93 A P a) (h2 : term196 A P a) : False.
Proof. exact (EQ_MP (@lem1073325 A P a h1 h2) (@lem1073176 A P a h1)). Qed.
Lemma lem1073327 {A : Type'} (P : type1160 A) (a : A) (h1 : P (@None A)) (h2 : term196 A P a) : (P (@None A)) = False.
Proof. exact (prop_ext (fun h3 : P (@None A) => @lem1073320 A P a h1 h2) (fun h3 : False => @lem1073161 A P h1)). Qed.
Lemma lem1073328 {A : Type'} (P : type1160 A) (a : A) (h1 : P (@None A)) (h2 : term196 A P a) : False.
Proof. exact (EQ_MP (@lem1073327 A P a h1 h2) (@lem1073161 A P h1)). Qed.
Lemma lem1073329 {A : Type'} (a : A) (P : type1160 A) (h1 : term93 A P a) (h2 : term185 A a P) : (term93 A P a) = False.
Proof. exact (prop_ext (fun h3 : term93 A P a => @lem1073322 A a P h1 h2) (fun h3 : False => @lem1073146 A P a h1)). Qed.
Lemma lem1073330 {A : Type'} (a : A) (P : type1160 A) (h1 : term93 A P a) (h2 : term185 A a P) : False.
Proof. exact (EQ_MP (@lem1073329 A a P h1 h2) (@lem1073146 A P a h1)). Qed.
Lemma lem1073331 {A : Type'} (a : A) (P : type1160 A) (h1 : P (@None A)) (h2 : term185 A a P) : (P (@None A)) = False.
Proof. exact (prop_ext (fun h3 : P (@None A) => @lem1073324 A a P h1 h2) (fun h3 : False => @lem1073131 A P h1)). Qed.
Lemma lem1073332 {A : Type'} (a : A) (P : type1160 A) (h1 : P (@None A)) (h2 : term185 A a P) : False.
Proof. exact (EQ_MP (@lem1073331 A a P h1 h2) (@lem1073131 A P h1)). Qed.
Lemma lem1073333 {A : Type'} (P : type1160 A) (a : A) (h1 : term196 A P a) : False.
Proof. exact (or_elim (@lem1073111 A P a h1) (fun h0 : P (@None A) => @lem1073328 A P a h0 h1) (fun h0 : term93 A P a => @lem1073326 A P a h0 h1)). Qed.
Lemma lem1073334 {A : Type'} (a : A) (P : type1160 A) (h1 : term185 A a P) : False.
Proof. exact (or_elim (@lem1073106 A a P h1) (fun h0 : P (@None A) => @lem1073332 A a P h0 h1) (fun h0 : term93 A P a => @lem1073330 A a P h0 h1)). Qed.
Lemma lem1073335 {A : Type'} (P : type1160 A) (a : A) (h1 : term215 A P a) : False.
Proof. exact (or_elim (@lem1073102 A P a h1) (fun h0 : term185 A a P => @lem1073334 A a P h0) (fun h0 : term196 A P a => @lem1073333 A P a h0)). Qed.
Lemma lem1073336 {A : Type'} (P : type1160 A) (a : A) (h1 : term215 A P a) : (term215 A P a) = False.
Proof. exact (prop_ext (fun h2 : term215 A P a => @lem1073335 A P a h1) (fun h2 : False => @lem1073102 A P a h1)). Qed.
Lemma lem1073337 {A : Type'} (P : type1160 A) (a : A) (h1 : term215 A P a) : False.
Proof. exact (EQ_MP (@lem1073336 A P a h1) (@lem1073102 A P a h1)). Qed.
Lemma lem1073338 {A : Type'} (P : type1160 A) (h1 : term128 A P) : False.
Proof. exact (ex_elim (@lem1073033 A P h1) (fun a : A => fun h0 : term217 A P a => @lem1073337 A P a h0)). Qed.
Lemma lem1073339 {A : Type'} (P : type1160 A) (h1 : term128 A P) : (term128 A P) = False.
Proof. exact (prop_ext (fun h2 : term128 A P => @lem1073338 A P h1) (fun h2 : False => @lem1072819 A P h1)). Qed.
Lemma lem1073340 {A : Type'} (P : type1160 A) (h1 : term128 A P) : False.
Proof. exact (EQ_MP (@lem1073339 A P h1) (@lem1072819 A P h1)). Qed.
Lemma lem1073341 {A : Type'} (P : type1160 A) : term127 A P.
Proof. exact (fun h0 : term128 A P => @lem1073340 A P h0). Qed.
Lemma lem1073342 {A : Type'} (P : type1160 A) : (term125 A P) = (term107 A P).
Proof. exact (EQ_MP (@lem1072818 A P) (@lem1073341 A P)). Qed.
Lemma lem1073347 {A : Type'} : term136 A.
Proof. exact (fun P : type1160 A => @lem1073342 A P). Qed.
Lemma lem1073348 {A : Type'} : term135 A.
Proof. exact (EQ_MP (@lem1072814 A) (@lem1073347 A)). Qed.
Lemma lem1073349 {A : Type'} (P : type1160 A) : term223 A P.
Proof. exact (@lem1073348 A P). Qed.
Lemma lem1073350 {A : Type'} (P : type1160 A) : (term223 A P) = (term127 A P).
Proof. exact (eq_refl (term223 A P)). Qed.
Lemma lem1073351 {A : Type'} (P : type1160 A) : term127 A P.
Proof. exact (EQ_MP (@lem1073350 A P) (@lem1073349 A P)). Qed.
Lemma lem1073353 {A : Type'} (P : type1160 A) : term127 A P.
Proof. exact (@lem1072722 A P (@lem1073351 A P)). Qed.
Lemma lem1073354 {A : Type'} (P : type1160 A) (h1 : term128 A P) : False.
Proof. exact (@lem1073353 A P (@lem1072706 A P h1)). Qed.
Lemma lem1073355 {A : Type'} (P : type1160 A) (h1 : term128 A P) : (term128 A P) = False.
Proof. exact (prop_ext (fun h2 : term128 A P => @lem1073354 A P h1) (fun h2 : False => @lem1072706 A P h1)). Qed.
Lemma lem1073356 {A : Type'} (P : type1160 A) (h1 : term128 A P) : False.
Proof. exact (EQ_MP (@lem1073355 A P h1) (@lem1072706 A P h1)). Qed.
Lemma lem1073357 {A : Type'} (P : type1160 A) : term127 A P.
Proof. exact (fun h0 : term128 A P => @lem1073356 A P h0). Qed.
Lemma lem1073358 {A : Type'} (P : type1160 A) : (term125 A P) = (term107 A P).
Proof. exact (EQ_MP (@lem1072705 A P) (@lem1073357 A P)). Qed.
Lemma lem1073359 {A : Type'} (P : type1160 A) : (term86 A P) = (term107 A P).
Proof. exact (EQ_MP (@lem1072701 A P) (@lem1073358 A P)). Qed.
Lemma lem1073360 {A : Type'} (P : type1160 A) : (term85 A P) = (term106 A P).
Proof. exact (EQ_MP (@lem1072650 A P) (@lem1073359 A P)). Qed.
Lemma lem1073365 {A : Type'} : term224 A.
Proof. exact (fun P : type1160 A => @lem1073360 A P). Qed.
