Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1103592_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1103259 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1103260 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1103261 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1103260 A B f) (@lem1103259 A B f)). Qed.
Lemma lem1103262 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1103261 A B f y). Qed.
Lemma lem1103263 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1103266 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : ALL2' = (term4 _25409 _25416 _17999).
Proof. exact (h1). Qed.
Lemma lem1103267 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1103268 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P) = (term5 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103266 _25409 _25416 ALL2' _17999 h1) (@lem1103267 _25409 _25416 P)). Qed.
Lemma lem1103270 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1103263 A B f y) (@lem1103262 A B f y)). Qed.
Lemma lem1103271 {_25409 _25416 : Type'} (f : type462 _25409 _25416) (y : type1413 _25409 _25416) : (term6 _25409 _25416 f y) = (f y).
Proof. exact (@lem1103270 (type1413 _25409 _25416) (type1135 _25409 _25416) f y). Qed.
Lemma lem1103272 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term7 _25409 _25416 _17999 P) = (term5 _25409 _25416 _17999 P).
Proof. exact (@lem1103271 _25409 _25416 (term4 _25409 _25416 _17999) P). Qed.
Lemma lem1103273 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (_17996 : type1413 _25409 _25416) : (term5 _25409 _25416 _17999 _17996) = (term8 _25409 _25416 _17999 _17996).
Proof. exact (eq_refl (term5 _25409 _25416 _17999 _17996)). Qed.
Lemma lem1103274 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) : (term9 _25409 _25416 _17999) = (term4 _25409 _25416 _17999).
Proof. exact (fun_ext (fun _17996 : type1413 _25409 _25416 => @lem1103273 _25409 _25416 _17999 _17996)). Qed.
Lemma lem1103275 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1103276 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term7 _25409 _25416 _17999 P) = (term5 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103274 _25409 _25416 _17999) (@lem1103275 _25409 _25416 P)). Qed.
Lemma lem1103277 {_25409 _25416 : Type'} : (@eq ((list _25409) -> (list _25416) -> Prop)) = (@eq ((list _25409) -> (list _25416) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25409) -> (list _25416) -> Prop))). Qed.
Lemma lem1103278 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term10 _25409 _25416 _17999 P) = (term11 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103277 _25409 _25416) (@lem1103276 _25409 _25416 _17999 P)). Qed.
Lemma lem1103279 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term5 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P).
Proof. exact (eq_refl (term5 _25409 _25416 _17999 P)). Qed.
Lemma lem1103280 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : ((term7 _25409 _25416 _17999 P) = (term5 _25409 _25416 _17999 P)) = ((term5 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P)).
Proof. exact (MK_COMB (@lem1103278 _25409 _25416 _17999 P) (@lem1103279 _25409 _25416 _17999 P)). Qed.
Lemma lem1103281 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term5 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P).
Proof. exact (EQ_MP (@lem1103280 _25409 _25416 _17999 P) (@lem1103272 _25409 _25416 _17999 P)). Qed.
Lemma lem1103282 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P) = (term8 _25409 _25416 _17999 P).
Proof. exact (TRANS (@lem1103268 _25409 _25416 P ALL2' _17999 h1) (@lem1103281 _25409 _25416 _17999 P)). Qed.
Lemma lem1103283 {_25409 : Type'} : (@nil _25409) = (@nil _25409).
Proof. exact (eq_refl (@nil _25409)). Qed.
Lemma lem1103284 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P (@nil _25409)) = (term12 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103282 _25409 _25416 P ALL2' _17999 h1) (@lem1103283 _25409)). Qed.
Lemma lem1103286 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1103263 A B f y) (@lem1103262 A B f y)). Qed.
Lemma lem1103287 {_25409 _25416 : Type'} (f : type1135 _25409 _25416) (y : list _25409) : (term13 _25409 _25416 f y) = (f y).
Proof. exact (@lem1103286 (list _25409) (type1143 _25416) f y). Qed.
Lemma lem1103288 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term14 _25409 _25416 _17999 P) = (term12 _25409 _25416 _17999 P).
Proof. exact (@lem1103287 _25409 _25416 (term8 _25409 _25416 _17999 P) (@nil _25409)). Qed.
Lemma lem1103289 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (_17997 : list _25409) (P : type1413 _25409 _25416) : (term15 _25409 _25416 _17999 P _17997) = (term16 _25409 _25416 _17999 _17997 P).
Proof. exact (eq_refl (term15 _25409 _25416 _17999 P _17997)). Qed.
Lemma lem1103290 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term17 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P).
Proof. exact (fun_ext (fun _17997 : list _25409 => @lem1103289 _25409 _25416 _17999 _17997 P)). Qed.
Lemma lem1103291 {_25409 : Type'} : (@nil _25409) = (@nil _25409).
Proof. exact (eq_refl (@nil _25409)). Qed.
Lemma lem1103292 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term14 _25409 _25416 _17999 P) = (term12 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103290 _25409 _25416 _17999 P) (@lem1103291 _25409)). Qed.
Lemma lem1103293 {_25416 : Type'} : (@eq ((list _25416) -> Prop)) = (@eq ((list _25416) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25416) -> Prop))). Qed.
Lemma lem1103294 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term18 _25409 _25416 _17999 P) = (term19 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103293 _25416) (@lem1103292 _25409 _25416 _17999 P)). Qed.
Lemma lem1103295 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term12 _25409 _25416 _17999 P) = (term20 _25409 _25416 _17999 P).
Proof. exact (eq_refl (term12 _25409 _25416 _17999 P)). Qed.
Lemma lem1103296 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : ((term14 _25409 _25416 _17999 P) = (term12 _25409 _25416 _17999 P)) = ((term12 _25409 _25416 _17999 P) = (term20 _25409 _25416 _17999 P)).
Proof. exact (MK_COMB (@lem1103294 _25409 _25416 _17999 P) (@lem1103295 _25409 _25416 _17999 P)). Qed.
Lemma lem1103297 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term12 _25409 _25416 _17999 P) = (term20 _25409 _25416 _17999 P).
Proof. exact (EQ_MP (@lem1103296 _25409 _25416 _17999 P) (@lem1103288 _25409 _25416 _17999 P)). Qed.
Lemma lem1103298 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P (@nil _25409)) = (term20 _25409 _25416 _17999 P).
Proof. exact (TRANS (@lem1103284 _25409 _25416 P ALL2' _17999 h1) (@lem1103297 _25409 _25416 _17999 P)). Qed.
Lemma lem1103299 {_25416 : Type'} (l2 : list _25416) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1103300 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P (@nil _25409) l2) = (term21 _25409 _25416 _17999 P l2).
Proof. exact (MK_COMB (@lem1103298 _25409 _25416 P ALL2' _17999 h1) (@lem1103299 _25416 l2)). Qed.
Lemma lem1103302 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1103263 A B f y) (@lem1103262 A B f y)). Qed.
Lemma lem1103303 {_25416 : Type'} (f : type1143 _25416) (y : list _25416) : (term22 _25416 f y) = (f y).
Proof. exact (@lem1103302 (list _25416) Prop f y). Qed.
Lemma lem1103304 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (l2 : list _25416) : (term23 _25409 _25416 _17999 P l2) = (term21 _25409 _25416 _17999 P l2).
Proof. exact (@lem1103303 _25416 (term20 _25409 _25416 _17999 P) l2). Qed.
Lemma lem1103305 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (_17998 : list _25416) : (term21 _25409 _25416 _17999 P _17998) = (_17999 (@nil _25409) P _17998).
Proof. exact (eq_refl (term21 _25409 _25416 _17999 P _17998)). Qed.
Lemma lem1103306 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term24 _25409 _25416 _17999 P) = (term20 _25409 _25416 _17999 P).
Proof. exact (fun_ext (fun _17998 : list _25416 => @lem1103305 _25409 _25416 _17999 P _17998)). Qed.
Lemma lem1103307 {_25416 : Type'} (l2 : list _25416) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1103308 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (l2 : list _25416) : (term23 _25409 _25416 _17999 P l2) = (term21 _25409 _25416 _17999 P l2).
Proof. exact (MK_COMB (@lem1103306 _25409 _25416 _17999 P) (@lem1103307 _25416 l2)). Qed.
Lemma lem1103309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1103310 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (l2 : list _25416) : (term25 _25409 _25416 _17999 P l2) = (term26 _25409 _25416 _17999 P l2).
Proof. exact (MK_COMB (@lem1103309) (@lem1103308 _25409 _25416 _17999 P l2)). Qed.
Lemma lem1103311 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (l2 : list _25416) : (term21 _25409 _25416 _17999 P l2) = (_17999 (@nil _25409) P l2).
Proof. exact (eq_refl (term21 _25409 _25416 _17999 P l2)). Qed.
Lemma lem1103312 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (l2 : list _25416) : ((term23 _25409 _25416 _17999 P l2) = (term21 _25409 _25416 _17999 P l2)) = ((term21 _25409 _25416 _17999 P l2) = (_17999 (@nil _25409) P l2)).
Proof. exact (MK_COMB (@lem1103310 _25409 _25416 _17999 P l2) (@lem1103311 _25409 _25416 _17999 P l2)). Qed.
Lemma lem1103313 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (l2 : list _25416) : (term21 _25409 _25416 _17999 P l2) = (_17999 (@nil _25409) P l2).
Proof. exact (EQ_MP (@lem1103312 _25409 _25416 _17999 P l2) (@lem1103304 _25409 _25416 _17999 P l2)). Qed.
Lemma lem1103314 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P (@nil _25409) l2) = (_17999 (@nil _25409) P l2).
Proof. exact (TRANS (@lem1103300 _25409 _25416 P l2 ALL2' _17999 h1) (@lem1103313 _25409 _25416 _17999 P l2)). Qed.
Lemma lem1103315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1103316 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term27 _25409 _25416 ALL2' P l2) = (term28 _25409 _25416 _17999 P l2).
Proof. exact (MK_COMB (@lem1103315) (@lem1103314 _25409 _25416 P l2 ALL2' _17999 h1)). Qed.
Lemma lem1103317 {_25416 : Type'} (l2 : list _25416) : (l2 = (@nil _25416)) = (l2 = (@nil _25416)).
Proof. exact (eq_refl (l2 = (@nil _25416))). Qed.
Lemma lem1103318 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : ((ALL2' P (@nil _25409) l2) = (l2 = (@nil _25416))) = ((_17999 (@nil _25409) P l2) = (l2 = (@nil _25416))).
Proof. exact (MK_COMB (@lem1103316 _25409 _25416 P l2 ALL2' _17999 h1) (@lem1103317 _25416 l2)). Qed.
Lemma lem1103319 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term29 _25409 _25416 ALL2' P) = (term30 _25409 _25416 _17999 P).
Proof. exact (fun_ext (fun l2 : list _25416 => @lem1103318 _25409 _25416 P l2 ALL2' _17999 h1)). Qed.
Lemma lem1103320 {_25416 : Type'} : (@all (list _25416)) = (@all (list _25416)).
Proof. exact (eq_refl (@all (list _25416))). Qed.
Lemma lem1103321 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term31 _25409 _25416 ALL2' P) = (term32 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103320 _25416) (@lem1103319 _25409 _25416 P ALL2' _17999 h1)). Qed.
Lemma lem1103322 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term33 _25409 _25416 ALL2') = (term34 _25409 _25416 _17999).
Proof. exact (fun_ext (fun P : type1413 _25409 _25416 => @lem1103321 _25409 _25416 P ALL2' _17999 h1)). Qed.
Lemma lem1103323 {_25409 _25416 : Type'} : (@all (_25409 -> _25416 -> Prop)) = (@all (_25409 -> _25416 -> Prop)).
Proof. exact (eq_refl (@all (_25409 -> _25416 -> Prop))). Qed.
Lemma lem1103324 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term35 _25409 _25416 ALL2') = (term36 _25409 _25416 _17999).
Proof. exact (MK_COMB (@lem1103323 _25409 _25416) (@lem1103322 _25409 _25416 ALL2' _17999 h1)). Qed.
Lemma lem1103325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1103326 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term37 _25409 _25416 ALL2') = (term38 _25409 _25416 _17999).
Proof. exact (MK_COMB (@lem1103325) (@lem1103324 _25409 _25416 ALL2' _17999 h1)). Qed.
Lemma lem1103328 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : ALL2' = (term4 _25409 _25416 _17999).
Proof. exact (h1). Qed.
Lemma lem1103329 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1103330 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P) = (term5 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103328 _25409 _25416 ALL2' _17999 h1) (@lem1103329 _25409 _25416 P)). Qed.
Lemma lem1103332 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1103263 A B f y) (@lem1103262 A B f y)). Qed.
Lemma lem1103333 {_25409 _25416 : Type'} (f : type462 _25409 _25416) (y : type1413 _25409 _25416) : (term6 _25409 _25416 f y) = (f y).
Proof. exact (@lem1103332 (type1413 _25409 _25416) (type1135 _25409 _25416) f y). Qed.
Lemma lem1103334 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term7 _25409 _25416 _17999 P) = (term5 _25409 _25416 _17999 P).
Proof. exact (@lem1103333 _25409 _25416 (term4 _25409 _25416 _17999) P). Qed.
Lemma lem1103335 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (_17996 : type1413 _25409 _25416) : (term5 _25409 _25416 _17999 _17996) = (term8 _25409 _25416 _17999 _17996).
Proof. exact (eq_refl (term5 _25409 _25416 _17999 _17996)). Qed.
Lemma lem1103336 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) : (term9 _25409 _25416 _17999) = (term4 _25409 _25416 _17999).
Proof. exact (fun_ext (fun _17996 : type1413 _25409 _25416 => @lem1103335 _25409 _25416 _17999 _17996)). Qed.
Lemma lem1103337 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1103338 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term7 _25409 _25416 _17999 P) = (term5 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103336 _25409 _25416 _17999) (@lem1103337 _25409 _25416 P)). Qed.
Lemma lem1103339 {_25409 _25416 : Type'} : (@eq ((list _25409) -> (list _25416) -> Prop)) = (@eq ((list _25409) -> (list _25416) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25409) -> (list _25416) -> Prop))). Qed.
Lemma lem1103340 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term10 _25409 _25416 _17999 P) = (term11 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103339 _25409 _25416) (@lem1103338 _25409 _25416 _17999 P)). Qed.
Lemma lem1103341 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term5 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P).
Proof. exact (eq_refl (term5 _25409 _25416 _17999 P)). Qed.
Lemma lem1103342 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : ((term7 _25409 _25416 _17999 P) = (term5 _25409 _25416 _17999 P)) = ((term5 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P)).
Proof. exact (MK_COMB (@lem1103340 _25409 _25416 _17999 P) (@lem1103341 _25409 _25416 _17999 P)). Qed.
Lemma lem1103343 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term5 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P).
Proof. exact (EQ_MP (@lem1103342 _25409 _25416 _17999 P) (@lem1103334 _25409 _25416 _17999 P)). Qed.
Lemma lem1103344 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P) = (term8 _25409 _25416 _17999 P).
Proof. exact (TRANS (@lem1103330 _25409 _25416 P ALL2' _17999 h1) (@lem1103343 _25409 _25416 _17999 P)). Qed.
Lemma lem1103345 {_25409 : Type'} (h1' : _25409) (t1 : list _25409) : (@cons _25409 h1' t1) = (@cons _25409 h1' t1).
Proof. exact (eq_refl (@cons _25409 h1' t1)). Qed.
Lemma lem1103346 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (h1' : _25409) (t1 : list _25409) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term39 _25409 _25416 ALL2' P h1' t1) = (term40 _25409 _25416 _17999 P h1' t1).
Proof. exact (MK_COMB (@lem1103344 _25409 _25416 P ALL2' _17999 h1) (@lem1103345 _25409 h1' t1)). Qed.
Lemma lem1103348 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1103263 A B f y) (@lem1103262 A B f y)). Qed.
Lemma lem1103349 {_25409 _25416 : Type'} (f : type1135 _25409 _25416) (y : list _25409) : (term13 _25409 _25416 f y) = (f y).
Proof. exact (@lem1103348 (list _25409) (type1143 _25416) f y). Qed.
Lemma lem1103350 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (h1' : _25409) (t1 : list _25409) : (term41 _25409 _25416 _17999 P h1' t1) = (term40 _25409 _25416 _17999 P h1' t1).
Proof. exact (@lem1103349 _25409 _25416 (term8 _25409 _25416 _17999 P) (@cons _25409 h1' t1)). Qed.
Lemma lem1103351 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (_17997 : list _25409) (P : type1413 _25409 _25416) : (term15 _25409 _25416 _17999 P _17997) = (term16 _25409 _25416 _17999 _17997 P).
Proof. exact (eq_refl (term15 _25409 _25416 _17999 P _17997)). Qed.
Lemma lem1103352 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term17 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P).
Proof. exact (fun_ext (fun _17997 : list _25409 => @lem1103351 _25409 _25416 _17999 _17997 P)). Qed.
Lemma lem1103353 {_25409 : Type'} (h1' : _25409) (t1 : list _25409) : (@cons _25409 h1' t1) = (@cons _25409 h1' t1).
Proof. exact (eq_refl (@cons _25409 h1' t1)). Qed.
Lemma lem1103354 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (h1' : _25409) (t1 : list _25409) : (term41 _25409 _25416 _17999 P h1' t1) = (term40 _25409 _25416 _17999 P h1' t1).
Proof. exact (MK_COMB (@lem1103352 _25409 _25416 _17999 P) (@lem1103353 _25409 h1' t1)). Qed.
Lemma lem1103355 {_25416 : Type'} : (@eq ((list _25416) -> Prop)) = (@eq ((list _25416) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25416) -> Prop))). Qed.
Lemma lem1103356 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (h1' : _25409) (t1 : list _25409) : (term42 _25409 _25416 _17999 P h1' t1) = (term43 _25409 _25416 _17999 P h1' t1).
Proof. exact (MK_COMB (@lem1103355 _25416) (@lem1103354 _25409 _25416 _17999 P h1' t1)). Qed.
Lemma lem1103357 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) : (term40 _25409 _25416 _17999 P h1' t1) = (term44 _25409 _25416 _17999 h1' t1 P).
Proof. exact (eq_refl (term40 _25409 _25416 _17999 P h1' t1)). Qed.
Lemma lem1103358 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) : ((term41 _25409 _25416 _17999 P h1' t1) = (term40 _25409 _25416 _17999 P h1' t1)) = ((term40 _25409 _25416 _17999 P h1' t1) = (term44 _25409 _25416 _17999 h1' t1 P)).
Proof. exact (MK_COMB (@lem1103356 _25409 _25416 _17999 P h1' t1) (@lem1103357 _25409 _25416 _17999 h1' t1 P)). Qed.
Lemma lem1103359 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) : (term40 _25409 _25416 _17999 P h1' t1) = (term44 _25409 _25416 _17999 h1' t1 P).
Proof. exact (EQ_MP (@lem1103358 _25409 _25416 _17999 h1' t1 P) (@lem1103350 _25409 _25416 _17999 P h1' t1)). Qed.
Lemma lem1103360 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term39 _25409 _25416 ALL2' P h1' t1) = (term44 _25409 _25416 _17999 h1' t1 P).
Proof. exact (TRANS (@lem1103346 _25409 _25416 P h1' t1 ALL2' _17999 h1) (@lem1103359 _25409 _25416 _17999 h1' t1 P)). Qed.
Lemma lem1103361 {_25416 : Type'} (l2 : list _25416) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1103362 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term45 _25409 _25416 ALL2' P h1' t1 l2) = (term46 _25409 _25416 _17999 h1' t1 P l2).
Proof. exact (MK_COMB (@lem1103360 _25409 _25416 h1' t1 P ALL2' _17999 h1) (@lem1103361 _25416 l2)). Qed.
Lemma lem1103364 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1103263 A B f y) (@lem1103262 A B f y)). Qed.
Lemma lem1103365 {_25416 : Type'} (f : type1143 _25416) (y : list _25416) : (term22 _25416 f y) = (f y).
Proof. exact (@lem1103364 (list _25416) Prop f y). Qed.
Lemma lem1103366 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term47 _25409 _25416 _17999 h1' t1 P l2) = (term46 _25409 _25416 _17999 h1' t1 P l2).
Proof. exact (@lem1103365 _25416 (term44 _25409 _25416 _17999 h1' t1 P) l2). Qed.
Lemma lem1103367 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (_17998 : list _25416) : (term46 _25409 _25416 _17999 h1' t1 P _17998) = (term48 _25409 _25416 _17999 h1' t1 P _17998).
Proof. exact (eq_refl (term46 _25409 _25416 _17999 h1' t1 P _17998)). Qed.
Lemma lem1103368 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) : (term49 _25409 _25416 _17999 h1' t1 P) = (term44 _25409 _25416 _17999 h1' t1 P).
Proof. exact (fun_ext (fun _17998 : list _25416 => @lem1103367 _25409 _25416 _17999 h1' t1 P _17998)). Qed.
Lemma lem1103369 {_25416 : Type'} (l2 : list _25416) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1103370 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term47 _25409 _25416 _17999 h1' t1 P l2) = (term46 _25409 _25416 _17999 h1' t1 P l2).
Proof. exact (MK_COMB (@lem1103368 _25409 _25416 _17999 h1' t1 P) (@lem1103369 _25416 l2)). Qed.
Lemma lem1103371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1103372 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term50 _25409 _25416 _17999 h1' t1 P l2) = (term51 _25409 _25416 _17999 h1' t1 P l2).
Proof. exact (MK_COMB (@lem1103371) (@lem1103370 _25409 _25416 _17999 h1' t1 P l2)). Qed.
Lemma lem1103373 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term46 _25409 _25416 _17999 h1' t1 P l2) = (term48 _25409 _25416 _17999 h1' t1 P l2).
Proof. exact (eq_refl (term46 _25409 _25416 _17999 h1' t1 P l2)). Qed.
Lemma lem1103374 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : ((term47 _25409 _25416 _17999 h1' t1 P l2) = (term46 _25409 _25416 _17999 h1' t1 P l2)) = ((term46 _25409 _25416 _17999 h1' t1 P l2) = (term48 _25409 _25416 _17999 h1' t1 P l2)).
Proof. exact (MK_COMB (@lem1103372 _25409 _25416 _17999 h1' t1 P l2) (@lem1103373 _25409 _25416 _17999 h1' t1 P l2)). Qed.
Lemma lem1103375 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term46 _25409 _25416 _17999 h1' t1 P l2) = (term48 _25409 _25416 _17999 h1' t1 P l2).
Proof. exact (EQ_MP (@lem1103374 _25409 _25416 _17999 h1' t1 P l2) (@lem1103366 _25409 _25416 _17999 h1' t1 P l2)). Qed.
Lemma lem1103376 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term45 _25409 _25416 ALL2' P h1' t1 l2) = (term48 _25409 _25416 _17999 h1' t1 P l2).
Proof. exact (TRANS (@lem1103362 _25409 _25416 h1' t1 P l2 ALL2' _17999 h1) (@lem1103375 _25409 _25416 _17999 h1' t1 P l2)). Qed.
Lemma lem1103377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1103378 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term52 _25409 _25416 ALL2' P h1' t1 l2) = (term53 _25409 _25416 _17999 h1' t1 P l2).
Proof. exact (MK_COMB (@lem1103377) (@lem1103376 _25409 _25416 h1' t1 P l2 ALL2' _17999 h1)). Qed.
Lemma lem1103380 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : ALL2' = (term4 _25409 _25416 _17999).
Proof. exact (h1). Qed.
Lemma lem1103381 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1103382 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P) = (term5 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103380 _25409 _25416 ALL2' _17999 h1) (@lem1103381 _25409 _25416 P)). Qed.
Lemma lem1103384 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1103263 A B f y) (@lem1103262 A B f y)). Qed.
Lemma lem1103385 {_25409 _25416 : Type'} (f : type462 _25409 _25416) (y : type1413 _25409 _25416) : (term6 _25409 _25416 f y) = (f y).
Proof. exact (@lem1103384 (type1413 _25409 _25416) (type1135 _25409 _25416) f y). Qed.
Lemma lem1103386 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term7 _25409 _25416 _17999 P) = (term5 _25409 _25416 _17999 P).
Proof. exact (@lem1103385 _25409 _25416 (term4 _25409 _25416 _17999) P). Qed.
Lemma lem1103387 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (_17996 : type1413 _25409 _25416) : (term5 _25409 _25416 _17999 _17996) = (term8 _25409 _25416 _17999 _17996).
Proof. exact (eq_refl (term5 _25409 _25416 _17999 _17996)). Qed.
Lemma lem1103388 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) : (term9 _25409 _25416 _17999) = (term4 _25409 _25416 _17999).
Proof. exact (fun_ext (fun _17996 : type1413 _25409 _25416 => @lem1103387 _25409 _25416 _17999 _17996)). Qed.
Lemma lem1103389 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1103390 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term7 _25409 _25416 _17999 P) = (term5 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103388 _25409 _25416 _17999) (@lem1103389 _25409 _25416 P)). Qed.
Lemma lem1103391 {_25409 _25416 : Type'} : (@eq ((list _25409) -> (list _25416) -> Prop)) = (@eq ((list _25409) -> (list _25416) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25409) -> (list _25416) -> Prop))). Qed.
Lemma lem1103392 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term10 _25409 _25416 _17999 P) = (term11 _25409 _25416 _17999 P).
Proof. exact (MK_COMB (@lem1103391 _25409 _25416) (@lem1103390 _25409 _25416 _17999 P)). Qed.
Lemma lem1103393 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term5 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P).
Proof. exact (eq_refl (term5 _25409 _25416 _17999 P)). Qed.
Lemma lem1103394 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : ((term7 _25409 _25416 _17999 P) = (term5 _25409 _25416 _17999 P)) = ((term5 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P)).
Proof. exact (MK_COMB (@lem1103392 _25409 _25416 _17999 P) (@lem1103393 _25409 _25416 _17999 P)). Qed.
Lemma lem1103395 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term5 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P).
Proof. exact (EQ_MP (@lem1103394 _25409 _25416 _17999 P) (@lem1103386 _25409 _25416 _17999 P)). Qed.
Lemma lem1103396 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P) = (term8 _25409 _25416 _17999 P).
Proof. exact (TRANS (@lem1103382 _25409 _25416 P ALL2' _17999 h1) (@lem1103395 _25409 _25416 _17999 P)). Qed.
Lemma lem1103397 {_25409 : Type'} (t1 : list _25409) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem1103398 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (t1 : list _25409) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P t1) = (term15 _25409 _25416 _17999 P t1).
Proof. exact (MK_COMB (@lem1103396 _25409 _25416 P ALL2' _17999 h1) (@lem1103397 _25409 t1)). Qed.
Lemma lem1103400 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1103263 A B f y) (@lem1103262 A B f y)). Qed.
Lemma lem1103401 {_25409 _25416 : Type'} (f : type1135 _25409 _25416) (y : list _25409) : (term13 _25409 _25416 f y) = (f y).
Proof. exact (@lem1103400 (list _25409) (type1143 _25416) f y). Qed.
Lemma lem1103402 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (t1 : list _25409) : (term54 _25409 _25416 _17999 P t1) = (term15 _25409 _25416 _17999 P t1).
Proof. exact (@lem1103401 _25409 _25416 (term8 _25409 _25416 _17999 P) t1). Qed.
Lemma lem1103403 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (_17997 : list _25409) (P : type1413 _25409 _25416) : (term15 _25409 _25416 _17999 P _17997) = (term16 _25409 _25416 _17999 _17997 P).
Proof. exact (eq_refl (term15 _25409 _25416 _17999 P _17997)). Qed.
Lemma lem1103404 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term17 _25409 _25416 _17999 P) = (term8 _25409 _25416 _17999 P).
Proof. exact (fun_ext (fun _17997 : list _25409 => @lem1103403 _25409 _25416 _17999 _17997 P)). Qed.
Lemma lem1103405 {_25409 : Type'} (t1 : list _25409) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem1103406 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (t1 : list _25409) : (term54 _25409 _25416 _17999 P t1) = (term15 _25409 _25416 _17999 P t1).
Proof. exact (MK_COMB (@lem1103404 _25409 _25416 _17999 P) (@lem1103405 _25409 t1)). Qed.
Lemma lem1103407 {_25416 : Type'} : (@eq ((list _25416) -> Prop)) = (@eq ((list _25416) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25416) -> Prop))). Qed.
Lemma lem1103408 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (t1 : list _25409) : (term55 _25409 _25416 _17999 P t1) = (term56 _25409 _25416 _17999 P t1).
Proof. exact (MK_COMB (@lem1103407 _25416) (@lem1103406 _25409 _25416 _17999 P t1)). Qed.
Lemma lem1103409 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) : (term15 _25409 _25416 _17999 P t1) = (term16 _25409 _25416 _17999 t1 P).
Proof. exact (eq_refl (term15 _25409 _25416 _17999 P t1)). Qed.
Lemma lem1103410 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) : ((term54 _25409 _25416 _17999 P t1) = (term15 _25409 _25416 _17999 P t1)) = ((term15 _25409 _25416 _17999 P t1) = (term16 _25409 _25416 _17999 t1 P)).
Proof. exact (MK_COMB (@lem1103408 _25409 _25416 _17999 P t1) (@lem1103409 _25409 _25416 _17999 t1 P)). Qed.
Lemma lem1103411 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) : (term15 _25409 _25416 _17999 P t1) = (term16 _25409 _25416 _17999 t1 P).
Proof. exact (EQ_MP (@lem1103410 _25409 _25416 _17999 t1 P) (@lem1103402 _25409 _25416 _17999 P t1)). Qed.
Lemma lem1103412 {_25409 _25416 : Type'} (t1 : list _25409) (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (ALL2' P t1) = (term16 _25409 _25416 _17999 t1 P).
Proof. exact (TRANS (@lem1103398 _25409 _25416 P t1 ALL2' _17999 h1) (@lem1103411 _25409 _25416 _17999 t1 P)). Qed.
Lemma lem1103413 {_25416 : Type'} (l2 : list _25416) : (@tl _25416 l2) = (@tl _25416 l2).
Proof. exact (eq_refl (@tl _25416 l2)). Qed.
Lemma lem1103414 {_25409 _25416 : Type'} (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term57 _25409 _25416 ALL2' P t1 l2) = (term58 _25409 _25416 _17999 t1 P l2).
Proof. exact (MK_COMB (@lem1103412 _25409 _25416 t1 P ALL2' _17999 h1) (@lem1103413 _25416 l2)). Qed.
Lemma lem1103416 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1103263 A B f y) (@lem1103262 A B f y)). Qed.
Lemma lem1103417 {_25416 : Type'} (f : type1143 _25416) (y : list _25416) : (term22 _25416 f y) = (f y).
Proof. exact (@lem1103416 (list _25416) Prop f y). Qed.
Lemma lem1103418 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term59 _25409 _25416 _17999 t1 P l2) = (term58 _25409 _25416 _17999 t1 P l2).
Proof. exact (@lem1103417 _25416 (term16 _25409 _25416 _17999 t1 P) (@tl _25416 l2)). Qed.
Lemma lem1103419 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) (_17998 : list _25416) : (term60 _25409 _25416 _17999 t1 P _17998) = (_17999 t1 P _17998).
Proof. exact (eq_refl (term60 _25409 _25416 _17999 t1 P _17998)). Qed.
Lemma lem1103420 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) : (term61 _25409 _25416 _17999 t1 P) = (term16 _25409 _25416 _17999 t1 P).
Proof. exact (fun_ext (fun _17998 : list _25416 => @lem1103419 _25409 _25416 _17999 t1 P _17998)). Qed.
Lemma lem1103421 {_25416 : Type'} (l2 : list _25416) : (@tl _25416 l2) = (@tl _25416 l2).
Proof. exact (eq_refl (@tl _25416 l2)). Qed.
Lemma lem1103422 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term59 _25409 _25416 _17999 t1 P l2) = (term58 _25409 _25416 _17999 t1 P l2).
Proof. exact (MK_COMB (@lem1103420 _25409 _25416 _17999 t1 P) (@lem1103421 _25416 l2)). Qed.
Lemma lem1103423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1103424 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term62 _25409 _25416 _17999 t1 P l2) = (term63 _25409 _25416 _17999 t1 P l2).
Proof. exact (MK_COMB (@lem1103423) (@lem1103422 _25409 _25416 _17999 t1 P l2)). Qed.
Lemma lem1103425 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term58 _25409 _25416 _17999 t1 P l2) = (term64 _25409 _25416 _17999 t1 P l2).
Proof. exact (eq_refl (term58 _25409 _25416 _17999 t1 P l2)). Qed.
Lemma lem1103426 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : ((term59 _25409 _25416 _17999 t1 P l2) = (term58 _25409 _25416 _17999 t1 P l2)) = ((term58 _25409 _25416 _17999 t1 P l2) = (term64 _25409 _25416 _17999 t1 P l2)).
Proof. exact (MK_COMB (@lem1103424 _25409 _25416 _17999 t1 P l2) (@lem1103425 _25409 _25416 _17999 t1 P l2)). Qed.
Lemma lem1103427 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term58 _25409 _25416 _17999 t1 P l2) = (term64 _25409 _25416 _17999 t1 P l2).
Proof. exact (EQ_MP (@lem1103426 _25409 _25416 _17999 t1 P l2) (@lem1103418 _25409 _25416 _17999 t1 P l2)). Qed.
Lemma lem1103428 {_25409 _25416 : Type'} (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term57 _25409 _25416 ALL2' P t1 l2) = (term64 _25409 _25416 _17999 t1 P l2).
Proof. exact (TRANS (@lem1103414 _25409 _25416 t1 P l2 ALL2' _17999 h1) (@lem1103427 _25409 _25416 _17999 t1 P l2)). Qed.
Lemma lem1103429 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (h1' : _25409) (l2 : list _25416) : (term65 _25409 _25416 P h1' l2) = (term65 _25409 _25416 P h1' l2).
Proof. exact (eq_refl (term65 _25409 _25416 P h1' l2)). Qed.
Lemma lem1103430 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term66 _25409 _25416 h1' ALL2' P t1 l2) = (term67 _25409 _25416 h1' _17999 t1 P l2).
Proof. exact (MK_COMB (@lem1103429 _25409 _25416 P h1' l2) (@lem1103428 _25409 _25416 t1 P l2 ALL2' _17999 h1)). Qed.
Lemma lem1103431 {_25416 : Type'} (l2 : list _25416) : (term68 _25416 l2) = (term68 _25416 l2).
Proof. exact (eq_refl (term68 _25416 l2)). Qed.
Lemma lem1103432 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term69 _25409 _25416 h1' ALL2' P t1 l2) = (term70 _25409 _25416 h1' _17999 t1 P l2).
Proof. exact (MK_COMB (@lem1103431 _25416 l2) (@lem1103430 _25409 _25416 h1' t1 P l2 ALL2' _17999 h1)). Qed.
Lemma lem1103433 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : ((term45 _25409 _25416 ALL2' P h1' t1 l2) = (term69 _25409 _25416 h1' ALL2' P t1 l2)) = ((term48 _25409 _25416 _17999 h1' t1 P l2) = (term70 _25409 _25416 h1' _17999 t1 P l2)).
Proof. exact (MK_COMB (@lem1103378 _25409 _25416 h1' t1 P l2 ALL2' _17999 h1) (@lem1103432 _25409 _25416 h1' t1 P l2 ALL2' _17999 h1)). Qed.
Lemma lem1103434 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term71 _25409 _25416 h1' ALL2' P t1) = (term72 _25409 _25416 h1' _17999 t1 P).
Proof. exact (fun_ext (fun l2 : list _25416 => @lem1103433 _25409 _25416 h1' t1 P l2 ALL2' _17999 h1)). Qed.
Lemma lem1103435 {_25416 : Type'} : (@all (list _25416)) = (@all (list _25416)).
Proof. exact (eq_refl (@all (list _25416))). Qed.
Lemma lem1103436 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term73 _25409 _25416 h1' ALL2' P t1) = (term74 _25409 _25416 h1' _17999 t1 P).
Proof. exact (MK_COMB (@lem1103435 _25416) (@lem1103434 _25409 _25416 h1' t1 P ALL2' _17999 h1)). Qed.
Lemma lem1103437 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term75 _25409 _25416 h1' ALL2' P) = (term76 _25409 _25416 h1' _17999 P).
Proof. exact (fun_ext (fun t1 : list _25409 => @lem1103436 _25409 _25416 h1' t1 P ALL2' _17999 h1)). Qed.
Lemma lem1103438 {_25409 : Type'} : (@all (list _25409)) = (@all (list _25409)).
Proof. exact (eq_refl (@all (list _25409))). Qed.
Lemma lem1103439 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term77 _25409 _25416 h1' ALL2' P) = (term78 _25409 _25416 h1' _17999 P).
Proof. exact (MK_COMB (@lem1103438 _25409) (@lem1103437 _25409 _25416 h1' P ALL2' _17999 h1)). Qed.
Lemma lem1103440 {_25409 _25416 : Type'} (h1' : _25409) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term79 _25409 _25416 h1' ALL2') = (term80 _25409 _25416 h1' _17999).
Proof. exact (fun_ext (fun P : type1413 _25409 _25416 => @lem1103439 _25409 _25416 h1' P ALL2' _17999 h1)). Qed.
Lemma lem1103441 {_25409 _25416 : Type'} : (@all (_25409 -> _25416 -> Prop)) = (@all (_25409 -> _25416 -> Prop)).
Proof. exact (eq_refl (@all (_25409 -> _25416 -> Prop))). Qed.
Lemma lem1103442 {_25409 _25416 : Type'} (h1' : _25409) (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term81 _25409 _25416 h1' ALL2') = (term82 _25409 _25416 h1' _17999).
Proof. exact (MK_COMB (@lem1103441 _25409 _25416) (@lem1103440 _25409 _25416 h1' ALL2' _17999 h1)). Qed.
Lemma lem1103443 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term83 _25409 _25416 ALL2') = (term84 _25409 _25416 _17999).
Proof. exact (fun_ext (fun h1' : _25409 => @lem1103442 _25409 _25416 h1' ALL2' _17999 h1)). Qed.
Lemma lem1103444 {_25409 : Type'} : (@all _25409) = (@all _25409).
Proof. exact (eq_refl (@all _25409)). Qed.
Lemma lem1103445 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term85 _25409 _25416 ALL2') = (term86 _25409 _25416 _17999).
Proof. exact (MK_COMB (@lem1103444 _25409) (@lem1103443 _25409 _25416 ALL2' _17999 h1)). Qed.
Lemma lem1103446 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term87 _25409 _25416 ALL2') = (term88 _25409 _25416 _17999).
Proof. exact (MK_COMB (@lem1103326 _25409 _25416 ALL2' _17999 h1) (@lem1103445 _25409 _25416 ALL2' _17999 h1)). Qed.
Lemma lem1103447 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : (_17999 (@nil _25409)) = (term89 _25409 _25416)) : (_17999 (@nil _25409)) = (term89 _25409 _25416).
Proof. exact (h1). Qed.
Lemma lem1103448 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1103449 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : (_17999 (@nil _25409)) = (term89 _25409 _25416)) : (_17999 (@nil _25409) P) = (term90 _25409 _25416 P).
Proof. exact (MK_COMB (@lem1103447 _25409 _25416 _17999 h1) (@lem1103448 _25409 _25416 P)). Qed.
Lemma lem1103450 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : (term90 _25409 _25416 P) = (term91 _25416).
Proof. exact (eq_refl (term90 _25409 _25416 P)). Qed.
Lemma lem1103451 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : (term92 _25409 _25416 _17999 P) = (term92 _25409 _25416 _17999 P).
Proof. exact (eq_refl (term92 _25409 _25416 _17999 P)). Qed.
Lemma lem1103452 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) : ((_17999 (@nil _25409) P) = (term90 _25409 _25416 P)) = ((_17999 (@nil _25409) P) = (term91 _25416)).
Proof. exact (MK_COMB (@lem1103451 _25409 _25416 _17999 P) (@lem1103450 _25409 _25416 P)). Qed.
Lemma lem1103453 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : (_17999 (@nil _25409)) = (term89 _25409 _25416)) : (_17999 (@nil _25409) P) = (term91 _25416).
Proof. exact (EQ_MP (@lem1103452 _25409 _25416 _17999 P) (@lem1103449 _25409 _25416 P _17999 h1)). Qed.
Lemma lem1103454 {_25416 : Type'} (l2 : list _25416) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1103455 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) (_17999 : type1128 _25409 _25416) (h1 : (_17999 (@nil _25409)) = (term89 _25409 _25416)) : (_17999 (@nil _25409) P l2) = (term93 _25416 l2).
Proof. exact (MK_COMB (@lem1103453 _25409 _25416 P _17999 h1) (@lem1103454 _25416 l2)). Qed.
Lemma lem1103456 {_25416 : Type'} (l2 : list _25416) : (term93 _25416 l2) = (l2 = (@nil _25416)).
Proof. exact (eq_refl (term93 _25416 l2)). Qed.
Lemma lem1103457 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (l2 : list _25416) : (term28 _25409 _25416 _17999 P l2) = (term28 _25409 _25416 _17999 P l2).
Proof. exact (eq_refl (term28 _25409 _25416 _17999 P l2)). Qed.
Lemma lem1103458 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (P : type1413 _25409 _25416) (l2 : list _25416) : ((_17999 (@nil _25409) P l2) = (term93 _25416 l2)) = ((_17999 (@nil _25409) P l2) = (l2 = (@nil _25416))).
Proof. exact (MK_COMB (@lem1103457 _25409 _25416 _17999 P l2) (@lem1103456 _25416 l2)). Qed.
Lemma lem1103459 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) (_17999 : type1128 _25409 _25416) (h1 : (_17999 (@nil _25409)) = (term89 _25409 _25416)) : (_17999 (@nil _25409) P l2) = (l2 = (@nil _25416)).
Proof. exact (EQ_MP (@lem1103458 _25409 _25416 _17999 P l2) (@lem1103455 _25409 _25416 P l2 _17999 h1)). Qed.
Lemma lem1103460 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : (_17999 (@nil _25409)) = (term89 _25409 _25416)) : term32 _25409 _25416 _17999 P.
Proof. exact (fun l2 : list _25416 => @lem1103459 _25409 _25416 P l2 _17999 h1). Qed.
Lemma lem1103461 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : (_17999 (@nil _25409)) = (term89 _25409 _25416)) : term36 _25409 _25416 _17999.
Proof. exact (fun P : type1413 _25409 _25416 => @lem1103460 _25409 _25416 P _17999 h1). Qed.
Lemma lem1103462 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : term94 _25409 _25416 _17999.
Proof. exact (h1). Qed.
Lemma lem1103463 {_25409 _25416 : Type'} (h1' : _25409) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : term95 _25409 _25416 _17999 h1'.
Proof. exact (@lem1103462 _25409 _25416 _17999 h1 h1'). Qed.
Lemma lem1103464 {_25409 _25416 : Type'} (h1' : _25409) (_17999 : type1128 _25409 _25416) : (term95 _25409 _25416 _17999 h1') = (term96 _25409 _25416 h1' _17999).
Proof. exact (eq_refl (term95 _25409 _25416 _17999 h1')). Qed.
Lemma lem1103465 {_25409 _25416 : Type'} (h1' : _25409) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : term96 _25409 _25416 h1' _17999.
Proof. exact (EQ_MP (@lem1103464 _25409 _25416 h1' _17999) (@lem1103463 _25409 _25416 h1' _17999 h1)). Qed.
Lemma lem1103466 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : term97 _25409 _25416 h1' _17999 t1.
Proof. exact (@lem1103465 _25409 _25416 h1' _17999 h1 t1). Qed.
Lemma lem1103467 {_25409 _25416 : Type'} (h1' : _25409) (_17999 : type1128 _25409 _25416) (t1 : list _25409) : (term97 _25409 _25416 h1' _17999 t1) = ((term98 _25409 _25416 _17999 h1' t1) = (term99 _25409 _25416 h1' _17999 t1)).
Proof. exact (eq_refl (term97 _25409 _25416 h1' _17999 t1)). Qed.
Lemma lem1103468 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : (term98 _25409 _25416 _17999 h1' t1) = (term99 _25409 _25416 h1' _17999 t1).
Proof. exact (EQ_MP (@lem1103467 _25409 _25416 h1' _17999 t1) (@lem1103466 _25409 _25416 h1' t1 _17999 h1)). Qed.
Lemma lem1103469 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1103470 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : (term100 _25409 _25416 _17999 h1' t1 P) = (term101 _25409 _25416 h1' _17999 t1 P).
Proof. exact (MK_COMB (@lem1103468 _25409 _25416 h1' t1 _17999 h1) (@lem1103469 _25409 _25416 P)). Qed.
Lemma lem1103471 {_25409 _25416 : Type'} (h1' : _25409) (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) : (term101 _25409 _25416 h1' _17999 t1 P) = (term102 _25409 _25416 h1' _17999 t1 P).
Proof. exact (eq_refl (term101 _25409 _25416 h1' _17999 t1 P)). Qed.
Lemma lem1103472 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) : (term103 _25409 _25416 _17999 h1' t1 P) = (term103 _25409 _25416 _17999 h1' t1 P).
Proof. exact (eq_refl (term103 _25409 _25416 _17999 h1' t1 P)). Qed.
Lemma lem1103473 {_25409 _25416 : Type'} (h1' : _25409) (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) : ((term100 _25409 _25416 _17999 h1' t1 P) = (term101 _25409 _25416 h1' _17999 t1 P)) = ((term100 _25409 _25416 _17999 h1' t1 P) = (term102 _25409 _25416 h1' _17999 t1 P)).
Proof. exact (MK_COMB (@lem1103472 _25409 _25416 _17999 h1' t1 P) (@lem1103471 _25409 _25416 h1' _17999 t1 P)). Qed.
Lemma lem1103474 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : (term100 _25409 _25416 _17999 h1' t1 P) = (term102 _25409 _25416 h1' _17999 t1 P).
Proof. exact (EQ_MP (@lem1103473 _25409 _25416 h1' _17999 t1 P) (@lem1103470 _25409 _25416 h1' t1 P _17999 h1)). Qed.
Lemma lem1103475 {_25416 : Type'} (l2 : list _25416) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1103476 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : (term48 _25409 _25416 _17999 h1' t1 P l2) = (term104 _25409 _25416 h1' _17999 t1 P l2).
Proof. exact (MK_COMB (@lem1103474 _25409 _25416 h1' t1 P _17999 h1) (@lem1103475 _25416 l2)). Qed.
Lemma lem1103477 {_25409 _25416 : Type'} (h1' : _25409) (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term104 _25409 _25416 h1' _17999 t1 P l2) = (term70 _25409 _25416 h1' _17999 t1 P l2).
Proof. exact (eq_refl (term104 _25409 _25416 h1' _17999 t1 P l2)). Qed.
Lemma lem1103478 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : (term53 _25409 _25416 _17999 h1' t1 P l2) = (term53 _25409 _25416 _17999 h1' t1 P l2).
Proof. exact (eq_refl (term53 _25409 _25416 _17999 h1' t1 P l2)). Qed.
Lemma lem1103479 {_25409 _25416 : Type'} (h1' : _25409) (_17999 : type1128 _25409 _25416) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) : ((term48 _25409 _25416 _17999 h1' t1 P l2) = (term104 _25409 _25416 h1' _17999 t1 P l2)) = ((term48 _25409 _25416 _17999 h1' t1 P l2) = (term70 _25409 _25416 h1' _17999 t1 P l2)).
Proof. exact (MK_COMB (@lem1103478 _25409 _25416 _17999 h1' t1 P l2) (@lem1103477 _25409 _25416 h1' _17999 t1 P l2)). Qed.
Lemma lem1103480 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (l2 : list _25416) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : (term48 _25409 _25416 _17999 h1' t1 P l2) = (term70 _25409 _25416 h1' _17999 t1 P l2).
Proof. exact (EQ_MP (@lem1103479 _25409 _25416 h1' _17999 t1 P l2) (@lem1103476 _25409 _25416 h1' t1 P l2 _17999 h1)). Qed.
Lemma lem1103481 {_25409 _25416 : Type'} (h1' : _25409) (t1 : list _25409) (P : type1413 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : term74 _25409 _25416 h1' _17999 t1 P.
Proof. exact (fun l2 : list _25416 => @lem1103480 _25409 _25416 h1' t1 P l2 _17999 h1). Qed.
Lemma lem1103482 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : term78 _25409 _25416 h1' _17999 P.
Proof. exact (fun t1 : list _25409 => @lem1103481 _25409 _25416 h1' t1 P _17999 h1). Qed.
Lemma lem1103483 {_25409 _25416 : Type'} (h1' : _25409) (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : term82 _25409 _25416 h1' _17999.
Proof. exact (fun P : type1413 _25409 _25416 => @lem1103482 _25409 _25416 h1' P _17999 h1). Qed.
Lemma lem1103484 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term94 _25409 _25416 _17999) : term86 _25409 _25416 _17999.
Proof. exact (fun h1' : _25409 => @lem1103483 _25409 _25416 h1' _17999 h1). Qed.
Lemma lem1103485 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term105 _25409 _25416 _17999.
Proof. exact (h1). Qed.
Lemma lem1103486 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term94 _25409 _25416 _17999.
Proof. exact (proj2 (@lem1103485 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103487 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : (_17999 (@nil _25409)) = (term89 _25409 _25416).
Proof. exact (proj1 (@lem1103485 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103488 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : ((_17999 (@nil _25409)) = (term89 _25409 _25416)) = (term36 _25409 _25416 _17999).
Proof. exact (prop_ext (fun h2 : (_17999 (@nil _25409)) = (term89 _25409 _25416) => @lem1103461 _25409 _25416 _17999 h2) (fun h2 : term36 _25409 _25416 _17999 => @lem1103487 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103489 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term36 _25409 _25416 _17999.
Proof. exact (EQ_MP (@lem1103488 _25409 _25416 _17999 h1) (@lem1103487 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103490 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : (term94 _25409 _25416 _17999) = (term86 _25409 _25416 _17999).
Proof. exact (prop_ext (fun h2 : term94 _25409 _25416 _17999 => @lem1103484 _25409 _25416 _17999 h2) (fun h2 : term86 _25409 _25416 _17999 => @lem1103486 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103491 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term86 _25409 _25416 _17999.
Proof. exact (EQ_MP (@lem1103490 _25409 _25416 _17999 h1) (@lem1103486 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103492 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term88 _25409 _25416 _17999.
Proof. exact (conj (@lem1103489 _25409 _25416 _17999 h1) (@lem1103491 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103493 {A Z : Type'} (NIL' : Z) : term106 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1103494 {A Z : Type'} (NIL' : Z) : (term106 A Z NIL') = (term107 A Z NIL').
Proof. exact (eq_refl (term106 A Z NIL')). Qed.
Lemma lem1103495 {A Z : Type'} (NIL' : Z) : term107 A Z NIL'.
Proof. exact (EQ_MP (@lem1103494 A Z NIL') (@lem1103493 A Z NIL')). Qed.
Lemma lem1103496 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term108 A Z NIL' CONS'.
Proof. exact (@lem1103495 A Z NIL' CONS'). Qed.
Lemma lem1103497 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term108 A Z NIL' CONS') = (term109 A Z NIL' CONS').
Proof. exact (eq_refl (term108 A Z NIL' CONS')). Qed.
Lemma lem1103498 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term109 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1103497 A Z NIL' CONS') (@lem1103496 A Z NIL' CONS')). Qed.
Lemma lem1103499 {_25409 _25416 : Type'} (NIL' : type463 _25409 _25416) (CONS' : type1384 _25409 _25416) : term110 _25409 _25416 NIL' CONS'.
Proof. exact (@lem1103498 _25409 (type463 _25409 _25416) NIL' CONS'). Qed.
Lemma lem1103500 {_25409 _25416 : Type'} : term111 _25409 _25416.
Proof. exact (@lem1103499 _25409 _25416 (term89 _25409 _25416) (term112 _25409 _25416)). Qed.
Lemma lem1103501 {_25409 _25416 : Type'} (a0 : _25409) : (term113 _25409 _25416 a0) = (term114 _25409 _25416 a0).
Proof. exact (eq_refl (term113 _25409 _25416 a0)). Qed.
Lemma lem1103502 {_25409 : Type'} (a1 : list _25409) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1103503 {_25409 _25416 : Type'} (a0 : _25409) (a1 : list _25409) : (term115 _25409 _25416 a0 a1) = (term116 _25409 _25416 a0 a1).
Proof. exact (MK_COMB (@lem1103501 _25409 _25416 a0) (@lem1103502 _25409 a1)). Qed.
Lemma lem1103504 {_25409 _25416 : Type'} (a1 : list _25409) (a0 : _25409) : (term116 _25409 _25416 a0 a1) = (term117 _25409 _25416 a0).
Proof. exact (eq_refl (term116 _25409 _25416 a0 a1)). Qed.
Lemma lem1103505 {_25409 _25416 : Type'} (a1 : list _25409) (a0 : _25409) : (term115 _25409 _25416 a0 a1) = (term117 _25409 _25416 a0).
Proof. exact (TRANS (@lem1103503 _25409 _25416 a0 a1) (@lem1103504 _25409 _25416 a1 a0)). Qed.
Lemma lem1103506 {_25409 _25416 : Type'} (fn : type1128 _25409 _25416) (a1 : list _25409) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1103507 {_25409 _25416 : Type'} (a0 : _25409) (fn : type1128 _25409 _25416) (a1 : list _25409) : (term118 _25409 _25416 a0 fn a1) = (term119 _25409 _25416 a0 fn a1).
Proof. exact (MK_COMB (@lem1103505 _25409 _25416 a1 a0) (@lem1103506 _25409 _25416 fn a1)). Qed.
Lemma lem1103508 {_25409 _25416 : Type'} (a0 : _25409) (fn : type1128 _25409 _25416) (a1 : list _25409) : (term119 _25409 _25416 a0 fn a1) = (term99 _25409 _25416 a0 fn a1).
Proof. exact (eq_refl (term119 _25409 _25416 a0 fn a1)). Qed.
Lemma lem1103509 {_25409 _25416 : Type'} (a0 : _25409) (fn : type1128 _25409 _25416) (a1 : list _25409) : (term118 _25409 _25416 a0 fn a1) = (term99 _25409 _25416 a0 fn a1).
Proof. exact (TRANS (@lem1103507 _25409 _25416 a0 fn a1) (@lem1103508 _25409 _25416 a0 fn a1)). Qed.
Lemma lem1103510 {_25409 _25416 : Type'} (fn : type1128 _25409 _25416) (a0 : _25409) (a1 : list _25409) : (term120 _25409 _25416 fn a0 a1) = (term120 _25409 _25416 fn a0 a1).
Proof. exact (eq_refl (term120 _25409 _25416 fn a0 a1)). Qed.
Lemma lem1103511 {_25409 _25416 : Type'} (a0 : _25409) (fn : type1128 _25409 _25416) (a1 : list _25409) : ((term98 _25409 _25416 fn a0 a1) = (term118 _25409 _25416 a0 fn a1)) = ((term98 _25409 _25416 fn a0 a1) = (term99 _25409 _25416 a0 fn a1)).
Proof. exact (MK_COMB (@lem1103510 _25409 _25416 fn a0 a1) (@lem1103509 _25409 _25416 a0 fn a1)). Qed.
Lemma lem1103512 {_25409 _25416 : Type'} (a0 : _25409) (fn : type1128 _25409 _25416) : (term121 _25409 _25416 a0 fn) = (term122 _25409 _25416 a0 fn).
Proof. exact (fun_ext (fun a1 : list _25409 => @lem1103511 _25409 _25416 a0 fn a1)). Qed.
Lemma lem1103513 {_25409 : Type'} : (@all (list _25409)) = (@all (list _25409)).
Proof. exact (eq_refl (@all (list _25409))). Qed.
Lemma lem1103514 {_25409 _25416 : Type'} (a0 : _25409) (fn : type1128 _25409 _25416) : (term123 _25409 _25416 a0 fn) = (term96 _25409 _25416 a0 fn).
Proof. exact (MK_COMB (@lem1103513 _25409) (@lem1103512 _25409 _25416 a0 fn)). Qed.
Lemma lem1103515 {_25409 _25416 : Type'} (fn : type1128 _25409 _25416) : (term124 _25409 _25416 fn) = (term125 _25409 _25416 fn).
Proof. exact (fun_ext (fun a0 : _25409 => @lem1103514 _25409 _25416 a0 fn)). Qed.
Lemma lem1103516 {_25409 : Type'} : (@all _25409) = (@all _25409).
Proof. exact (eq_refl (@all _25409)). Qed.
Lemma lem1103517 {_25409 _25416 : Type'} (fn : type1128 _25409 _25416) : (term126 _25409 _25416 fn) = (term94 _25409 _25416 fn).
Proof. exact (MK_COMB (@lem1103516 _25409) (@lem1103515 _25409 _25416 fn)). Qed.
Lemma lem1103518 {_25409 _25416 : Type'} (fn : type1128 _25409 _25416) : (term127 _25409 _25416 fn) = (term127 _25409 _25416 fn).
Proof. exact (eq_refl (term127 _25409 _25416 fn)). Qed.
Lemma lem1103519 {_25409 _25416 : Type'} (fn : type1128 _25409 _25416) : (term128 _25409 _25416 fn) = (term105 _25409 _25416 fn).
Proof. exact (MK_COMB (@lem1103518 _25409 _25416 fn) (@lem1103517 _25409 _25416 fn)). Qed.
Lemma lem1103520 {_25409 _25416 : Type'} : (term129 _25409 _25416) = (term130 _25409 _25416).
Proof. exact (fun_ext (fun fn : type1128 _25409 _25416 => @lem1103519 _25409 _25416 fn)). Qed.
Lemma lem1103521 {_25409 _25416 : Type'} : (@ex ((list _25409) -> (_25409 -> _25416 -> Prop) -> (list _25416) -> Prop)) = (@ex ((list _25409) -> (_25409 -> _25416 -> Prop) -> (list _25416) -> Prop)).
Proof. exact (eq_refl (@ex ((list _25409) -> (_25409 -> _25416 -> Prop) -> (list _25416) -> Prop))). Qed.
Lemma lem1103522 {_25409 _25416 : Type'} : (term111 _25409 _25416) = (term131 _25409 _25416).
Proof. exact (MK_COMB (@lem1103521 _25409 _25416) (@lem1103520 _25409 _25416)). Qed.
Lemma lem1103523 {_25409 _25416 : Type'} : term131 _25409 _25416.
Proof. exact (EQ_MP (@lem1103522 _25409 _25416) (@lem1103500 _25409 _25416)). Qed.
Lemma lem1103524 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term105 _25409 _25416 _17999.
Proof. exact (h1). Qed.
Lemma lem1103525 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term94 _25409 _25416 _17999.
Proof. exact (proj2 (@lem1103524 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103526 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : (_17999 (@nil _25409)) = (term89 _25409 _25416).
Proof. exact (proj1 (@lem1103524 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103527 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term105 _25409 _25416 _17999.
Proof. exact (conj (@lem1103526 _25409 _25416 _17999 h1) (@lem1103525 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103528 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term131 _25409 _25416.
Proof. exact (ex_intro (term130 _25409 _25416) _17999 (@lem1103527 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103529 {_25409 _25416 : Type'} (h1 : term131 _25409 _25416) : term131 _25409 _25416.
Proof. exact (h1). Qed.
Lemma lem1103530 {_25409 _25416 : Type'} (h1 : term131 _25409 _25416) : term131 _25409 _25416.
Proof. exact (ex_elim (@lem1103529 _25409 _25416 h1) (fun _17999 : type1128 _25409 _25416 => fun h0 : term130 _25409 _25416 _17999 => @lem1103528 _25409 _25416 _17999 h0)). Qed.
Lemma lem1103531 {_25409 _25416 : Type'} : (term131 _25409 _25416) = (term131 _25409 _25416).
Proof. exact (prop_ext (fun h1 : term131 _25409 _25416 => @lem1103530 _25409 _25416 h1) (fun h1 : term131 _25409 _25416 => @lem1103523 _25409 _25416)). Qed.
Lemma lem1103532 {_25409 _25416 : Type'} : term131 _25409 _25416.
Proof. exact (EQ_MP (@lem1103531 _25409 _25416) (@lem1103523 _25409 _25416)). Qed.
Lemma lem1103533 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term105 _25409 _25416 _17999) : term132 _25409 _25416.
Proof. exact (ex_intro (term133 _25409 _25416) _17999 (@lem1103492 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103534 {_25409 _25416 : Type'} (h1 : term131 _25409 _25416) : term131 _25409 _25416.
Proof. exact (h1). Qed.
Lemma lem1103535 {_25409 _25416 : Type'} (h1 : term131 _25409 _25416) : term132 _25409 _25416.
Proof. exact (ex_elim (@lem1103534 _25409 _25416 h1) (fun _17999 : type1128 _25409 _25416 => fun h0 : term130 _25409 _25416 _17999 => @lem1103533 _25409 _25416 _17999 h0)). Qed.
Lemma lem1103536 {_25409 _25416 : Type'} : (term131 _25409 _25416) = (term132 _25409 _25416).
Proof. exact (prop_ext (fun h1 : term131 _25409 _25416 => @lem1103535 _25409 _25416 h1) (fun h1 : term132 _25409 _25416 => @lem1103532 _25409 _25416)). Qed.
Lemma lem1103537 {_25409 _25416 : Type'} : term132 _25409 _25416.
Proof. exact (EQ_MP (@lem1103536 _25409 _25416) (@lem1103532 _25409 _25416)). Qed.
Lemma lem1103538 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term88 _25409 _25416 _17999) : term88 _25409 _25416 _17999.
Proof. exact (h1). Qed.
Lemma lem1103539 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : ALL2' = (term4 _25409 _25416 _17999)) : (term88 _25409 _25416 _17999) = (term87 _25409 _25416 ALL2').
Proof. exact (SYM (@lem1103446 _25409 _25416 ALL2' _17999 h1)). Qed.
Lemma lem1103540 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : term88 _25409 _25416 _17999) (h2 : ALL2' = (term4 _25409 _25416 _17999)) : term87 _25409 _25416 ALL2'.
Proof. exact (EQ_MP (@lem1103539 _25409 _25416 ALL2' _17999 h2) (@lem1103538 _25409 _25416 _17999 h1)). Qed.
Lemma lem1103541 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : term88 _25409 _25416 _17999) (h2 : ALL2' = (term4 _25409 _25416 _17999)) : term134 _25409 _25416.
Proof. exact (ex_intro (term135 _25409 _25416) ALL2' (@lem1103540 _25409 _25416 ALL2' _17999 h1 h2)). Qed.
Lemma lem1103542 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) : (term4 _25409 _25416 _17999) = (term4 _25409 _25416 _17999).
Proof. exact (eq_refl (term4 _25409 _25416 _17999)). Qed.
Lemma lem1103543 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) (_17999 : type1128 _25409 _25416) (h1 : term88 _25409 _25416 _17999) : term136 _25409 _25416 ALL2' _17999.
Proof. exact (fun h0 : ALL2' = (term4 _25409 _25416 _17999) => @lem1103541 _25409 _25416 ALL2' _17999 h1 h0). Qed.
Lemma lem1103544 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term88 _25409 _25416 _17999) : term137 _25409 _25416 _17999.
Proof. exact (@lem1103543 _25409 _25416 (term4 _25409 _25416 _17999) _17999 h1). Qed.
Lemma lem1103545 {_25409 _25416 : Type'} (_17999 : type1128 _25409 _25416) (h1 : term88 _25409 _25416 _17999) : term134 _25409 _25416.
Proof. exact (@lem1103544 _25409 _25416 _17999 h1 (@lem1103542 _25409 _25416 _17999)). Qed.
Lemma lem1103546 {_25409 _25416 : Type'} (h1 : term132 _25409 _25416) : term132 _25409 _25416.
Proof. exact (h1). Qed.
Lemma lem1103547 {_25409 _25416 : Type'} (h1 : term132 _25409 _25416) : term134 _25409 _25416.
Proof. exact (ex_elim (@lem1103546 _25409 _25416 h1) (fun _17999 : type1128 _25409 _25416 => fun h0 : term133 _25409 _25416 _17999 => @lem1103545 _25409 _25416 _17999 h0)). Qed.
Lemma lem1103548 {_25409 _25416 : Type'} : (term132 _25409 _25416) = (term134 _25409 _25416).
Proof. exact (prop_ext (fun h1 : term132 _25409 _25416 => @lem1103547 _25409 _25416 h1) (fun h1 : term134 _25409 _25416 => @lem1103537 _25409 _25416)). Qed.
Lemma lem1103549 {_25409 _25416 : Type'} : term134 _25409 _25416.
Proof. exact (EQ_MP (@lem1103548 _25409 _25416) (@lem1103537 _25409 _25416)). Qed.
Lemma lem1103550 {_25409 _25416 : Type'} : term138 _25409 _25416.
Proof. exact (fun _18003 : type1673 => @lem1103549 _25409 _25416). Qed.
Lemma lem1103551 {A B : Type'} (P : type1413 A B) : term139 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1103552 {A B : Type'} (P : type1413 A B) : (term139 A B P) = ((term140 A B P) = (term141 A B P)).
Proof. exact (eq_refl (term139 A B P)). Qed.
Lemma lem1103555 {A B : Type'} (P : type1413 A B) : (term140 A B P) = (term141 A B P).
Proof. exact (EQ_MP (@lem1103552 A B P) (@lem1103551 A B P)). Qed.
Lemma lem1103556 {_25409 _25416 : Type'} (P : type1281 _25409 _25416) : (term142 _25409 _25416 P) = (term143 _25409 _25416 P).
Proof. exact (@lem1103555 type1673 (type462 _25409 _25416) P). Qed.
Lemma lem1103557 {_25409 _25416 : Type'} : (term144 _25409 _25416) = (term145 _25409 _25416).
Proof. exact (@lem1103556 _25409 _25416 (term146 _25409 _25416)). Qed.
Lemma lem1103558 {_25409 _25416 : Type'} (_18003 : type1673) : (term147 _25409 _25416 _18003) = (term135 _25409 _25416).
Proof. exact (eq_refl (term147 _25409 _25416 _18003)). Qed.
Lemma lem1103559 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) : ALL2' = ALL2'.
Proof. exact (eq_refl ALL2'). Qed.
Lemma lem1103560 {_25409 _25416 : Type'} (_18003 : type1673) (ALL2' : type462 _25409 _25416) : (term148 _25409 _25416 _18003 ALL2') = (term149 _25409 _25416 ALL2').
Proof. exact (MK_COMB (@lem1103558 _25409 _25416 _18003) (@lem1103559 _25409 _25416 ALL2')). Qed.
Lemma lem1103561 {_25409 _25416 : Type'} (ALL2' : type462 _25409 _25416) : (term149 _25409 _25416 ALL2') = (term87 _25409 _25416 ALL2').
Proof. exact (eq_refl (term149 _25409 _25416 ALL2')). Qed.
Lemma lem1103562 {_25409 _25416 : Type'} (_18003 : type1673) (ALL2' : type462 _25409 _25416) : (term148 _25409 _25416 _18003 ALL2') = (term87 _25409 _25416 ALL2').
Proof. exact (TRANS (@lem1103560 _25409 _25416 _18003 ALL2') (@lem1103561 _25409 _25416 ALL2')). Qed.
Lemma lem1103563 {_25409 _25416 : Type'} (_18003 : type1673) : (term150 _25409 _25416 _18003) = (term135 _25409 _25416).
Proof. exact (fun_ext (fun ALL2' : type462 _25409 _25416 => @lem1103562 _25409 _25416 _18003 ALL2')). Qed.
Lemma lem1103564 {_25409 _25416 : Type'} : (@ex ((_25409 -> _25416 -> Prop) -> (list _25409) -> (list _25416) -> Prop)) = (@ex ((_25409 -> _25416 -> Prop) -> (list _25409) -> (list _25416) -> Prop)).
Proof. exact (eq_refl (@ex ((_25409 -> _25416 -> Prop) -> (list _25409) -> (list _25416) -> Prop))). Qed.
Lemma lem1103565 {_25409 _25416 : Type'} (_18003 : type1673) : (term151 _25409 _25416 _18003) = (term134 _25409 _25416).
Proof. exact (MK_COMB (@lem1103564 _25409 _25416) (@lem1103563 _25409 _25416 _18003)). Qed.
Lemma lem1103566 {_25409 _25416 : Type'} : (term152 _25409 _25416) = (term153 _25409 _25416).
Proof. exact (fun_ext (fun _18003 : type1673 => @lem1103565 _25409 _25416 _18003)). Qed.
Lemma lem1103567 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1103568 {_25409 _25416 : Type'} : (term144 _25409 _25416) = (term138 _25409 _25416).
Proof. exact (MK_COMB (@lem1103567) (@lem1103566 _25409 _25416)). Qed.
Lemma lem1103569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1103570 {_25409 _25416 : Type'} : (term154 _25409 _25416) = (term155 _25409 _25416).
Proof. exact (MK_COMB (@lem1103569) (@lem1103568 _25409 _25416)). Qed.
Lemma lem1103571 {_25409 _25416 : Type'} (_18003 : type1673) : (term147 _25409 _25416 _18003) = (term135 _25409 _25416).
Proof. exact (eq_refl (term147 _25409 _25416 _18003)). Qed.
Lemma lem1103572 {_25409 _25416 : Type'} (ALL2' : type1285 _25409 _25416) (_18003 : type1673) : (ALL2' _18003) = (ALL2' _18003).
Proof. exact (eq_refl (ALL2' _18003)). Qed.
Lemma lem1103573 {_25409 _25416 : Type'} (ALL2' : type1285 _25409 _25416) (_18003 : type1673) : (term156 _25409 _25416 ALL2' _18003) = (term157 _25409 _25416 ALL2' _18003).
Proof. exact (MK_COMB (@lem1103571 _25409 _25416 _18003) (@lem1103572 _25409 _25416 ALL2' _18003)). Qed.
Lemma lem1103574 {_25409 _25416 : Type'} (ALL2' : type1285 _25409 _25416) (_18003 : type1673) : (term157 _25409 _25416 ALL2' _18003) = (term158 _25409 _25416 ALL2' _18003).
Proof. exact (eq_refl (term157 _25409 _25416 ALL2' _18003)). Qed.
Lemma lem1103575 {_25409 _25416 : Type'} (ALL2' : type1285 _25409 _25416) (_18003 : type1673) : (term156 _25409 _25416 ALL2' _18003) = (term158 _25409 _25416 ALL2' _18003).
Proof. exact (TRANS (@lem1103573 _25409 _25416 ALL2' _18003) (@lem1103574 _25409 _25416 ALL2' _18003)). Qed.
Lemma lem1103576 {_25409 _25416 : Type'} (ALL2' : type1285 _25409 _25416) : (term159 _25409 _25416 ALL2') = (term160 _25409 _25416 ALL2').
Proof. exact (fun_ext (fun _18003 : type1673 => @lem1103575 _25409 _25416 ALL2' _18003)). Qed.
Lemma lem1103577 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1103578 {_25409 _25416 : Type'} (ALL2' : type1285 _25409 _25416) : (term161 _25409 _25416 ALL2') = (term162 _25409 _25416 ALL2').
Proof. exact (MK_COMB (@lem1103577) (@lem1103576 _25409 _25416 ALL2')). Qed.
Lemma lem1103579 {_25409 _25416 : Type'} : (term163 _25409 _25416) = (term164 _25409 _25416).
Proof. exact (fun_ext (fun ALL2' : type1285 _25409 _25416 => @lem1103578 _25409 _25416 ALL2')). Qed.
Lemma lem1103580 {_25409 _25416 : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (_25409 -> _25416 -> Prop) -> (list _25409) -> (list _25416) -> Prop)) = (@ex ((prod nat (prod nat (prod nat nat))) -> (_25409 -> _25416 -> Prop) -> (list _25409) -> (list _25416) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat nat))) -> (_25409 -> _25416 -> Prop) -> (list _25409) -> (list _25416) -> Prop))). Qed.
Lemma lem1103581 {_25409 _25416 : Type'} : (term145 _25409 _25416) = (term165 _25409 _25416).
Proof. exact (MK_COMB (@lem1103580 _25409 _25416) (@lem1103579 _25409 _25416)). Qed.
Lemma lem1103582 {_25409 _25416 : Type'} : ((term144 _25409 _25416) = (term145 _25409 _25416)) = ((term138 _25409 _25416) = (term165 _25409 _25416)).
Proof. exact (MK_COMB (@lem1103570 _25409 _25416) (@lem1103581 _25409 _25416)). Qed.
Lemma lem1103583 {_25409 _25416 : Type'} : (term138 _25409 _25416) = (term165 _25409 _25416).
Proof. exact (EQ_MP (@lem1103582 _25409 _25416) (@lem1103557 _25409 _25416)). Qed.
Lemma lem1103584 {_25409 _25416 : Type'} : term165 _25409 _25416.
Proof. exact (EQ_MP (@lem1103583 _25409 _25416) (@lem1103550 _25409 _25416)). Qed.
Lemma lem1103586 {A : Type'} : (@ex A) = (term166 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1103587 {_25409 _25416 : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (_25409 -> _25416 -> Prop) -> (list _25409) -> (list _25416) -> Prop)) = (term167 _25409 _25416).
Proof. exact (@lem1103586 (type1285 _25409 _25416)). Qed.
Lemma lem1103588 {_25409 _25416 : Type'} : (term164 _25409 _25416) = (term164 _25409 _25416).
Proof. exact (eq_refl (term164 _25409 _25416)). Qed.
Lemma lem1103589 {_25409 _25416 : Type'} : (term165 _25409 _25416) = (term168 _25409 _25416).
Proof. exact (MK_COMB (@lem1103587 _25409 _25416) (@lem1103588 _25409 _25416)). Qed.
Lemma lem1103590 {_25409 _25416 : Type'} : (term168 _25409 _25416) = (term169 _25409 _25416).
Proof. exact (eq_refl (term168 _25409 _25416)). Qed.
Lemma lem1103591 {_25409 _25416 : Type'} : (term165 _25409 _25416) = (term169 _25409 _25416).
Proof. exact (TRANS (@lem1103589 _25409 _25416) (@lem1103590 _25409 _25416)). Qed.
Lemma lem1103592 {_25409 _25416 : Type'} : term169 _25409 _25416.
Proof. exact (EQ_MP (@lem1103591 _25409 _25416) (@lem1103584 _25409 _25416)). Qed.
